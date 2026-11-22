"""Collect public Reviewed hospital reviews from the visible website."""

import argparse
import codecs
import csv
import hashlib
import json
import logging
import os
import re
import sys
import tempfile
import time
import unicodedata
from collections import Counter
from contextlib import contextmanager
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import urlsplit
from urllib.robotparser import RobotFileParser


ORIGIN = "https://reviewed.co.kr"
DEPARTMENTS = {
    '외과': ('reviewed_surgery', f'{ORIGIN}/ko/search/result?treatment=15'),
    '내과': ('reviewed_internal_medicine', f'{ORIGIN}/ko/search/result?treatment=9'),
    '이비인후과': ('reviewed_otolaryngology', f'{ORIGIN}/ko/search/result?treatment=8'),
    '정형외과': ('reviewed_orthopedics', f'{ORIGIN}/ko/search/result?treatment=5'),
    '치과': ('reviewed_dentistry', f'{ORIGIN}/ko/search/result?treatment=4'),
}
KST = timezone(timedelta(hours=9))
NULL = "NULL"
MAX_REVIEWS = 40
FIELDS = (
    "review_id", "review_text", "review_ai_score", "review_date", "review_language",
    "hospital_id", "hospital_name", "department", "address", "hospital_url",
    "review_count", "event_id", "event_mentioned", "event_type", "collected_at",
)
HOSPITAL_LINKS = 'a:has(.search-hospital-text):visible'
ROW_SELECTOR = '.detail-reviews .detail-review-row:visible'
LIST_MORE = 'button.search-more:visible'
LOG = logging.getLogger("reviewed")


class CollectionError(Exception):
    """A visible state or stored file could not be verified."""


class AccessStop(CollectionError):
    """An access or server limit applies to the whole collection."""


def now():
    return datetime.now(KST).isoformat(timespec="seconds")


def normalized(value):
    return " ".join(unicodedata.normalize("NFC", value or "").split())


def count_from(text):
    match = re.search(r"\d[\d,]*", text or "")
    return int(match[0].replace(",", "")) if match else None


def review_date(display, machine):
    if machine and re.fullmatch(r"\d{4}-\d{2}-\d{2}", machine):
        try:
            return date.fromisoformat(machine).isoformat()
        except ValueError:
            pass
    exact = re.fullmatch(r"(\d{4})[.\-/년]\s*(\d{1,2})[.\-/월]\s*(\d{1,2})[.일]?", display or "")
    if exact:
        try:
            return date(*(int(x) for x in exact.groups())).isoformat()
        except ValueError:
            pass
    return display or NULL


def language(text):
    if not text:
        return "unknown"
    groups = Counter()
    for char in text:
        if not char.isalpha():
            continue
        name = unicodedata.name(char, "")
        if name.startswith("HANGUL"):
            groups["ko"] += 1
        elif name.startswith(("HIRAGANA", "KATAKANA")):
            groups["ja"] += 1
        elif name.startswith(("CJK UNIFIED", "CJK COMPATIBILITY")):
            groups["zh"] += 1
        elif name.startswith('LATIN'):
            groups['en' if char.isascii() else 'other'] += 1
        else:
            groups['other'] += 1
    if groups['ja']:
        groups['ja'] += groups.pop('zh', 0)
    return groups.most_common(1)[0][0] if groups.total() else 'unknown'


IDENTIFIERS = re.compile(
    r"https?://\S+|\b[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}\b|(?<!\w)@[A-Za-z0-9_.-]+|"
    r"(?<!\d)\d{6}[-– ]?[1-8]\d{6}(?!\d)|"
    r"(?<!\d)(?:\+?82[ .-]?(?:\(0\))?[ .-]?(?:\(\d{1,2}\)|\d{1,2})|\(?0\d{1,2}\)?)[ .-]?\d{3,4}[ .-]?\d{4}(?!\d)|"
    r"(?:이름|성명|환자번호|차트번호|예약번호|연락처|전화번호|카카오톡\s*ID|계정|생년월일|집\s*주소)\s*[:：=]\s*[^,;\n]+|"
    r"[가-힣0-9]+(?:로|길)\s+\d+(?:[-–]\d+)?(?:\s+\d+호)?|"
    r"\d{1,4}동\s*\d{1,4}호|\d{1,3}\s*(?:세|살)(?=\s|[,.]|$)|"
    r"\d{2,4}\s*(?:년|[./-])\s*\d{1,2}\s*(?:월|[./-])\s*\d{1,2}\s*일?|"
    r"(?<![가-힣])[가-힣]{2,4}\s*(?=의사|교수(?:님)?|원장(?:님)?|선생님|간호사(?:님)?|씨\b|님께)|"
    r"\b(?:Dr\.?|Mr\.?|Ms\.?|Mrs\.?)\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+)?",
    re.IGNORECASE,
)
HEALTH = re.compile(
    r"암(?:을|이|으로|에|은|\s|$)|종양|결석|담석|진단\s*받|진단명|질환|질병|지병|병력|복용|처방|"
    r"항암|당뇨|고혈압|갑상선|갑상샘|치질|치핵|치루|치열|맹장|충수|담낭|담도|유방|유도분만|임신|임산부|수유|"
    r"정신질환|우울증|공황장애|자해|자살|성병|HIV|에이즈|조직\s*검사|유전자|수술(?:명|을\s*받|을?\s*했)|"
    r"암\s*\d기|\d+\s*mg\b|생리|배변|출혈|복통|시술\s*(?:받|했)|"
    r"\b(?:diagnos\w*|cancer|tumou?r|diabet\w*|pregnan\w*|miscarriage|gallstones?|thyroid|HIV|AIDS|"
    r"depression|anxiety disorder|my (?:surgery|operation|medication|condition))\b|"
    r"診断|診斷|癌症|癌|妊娠|手術|手术|懷孕|怀孕|抑郁|抑鬱|うつ病",
    re.IGNORECASE,
)


def redact(text):
    clean = IDENTIFIERS.sub('[개인정보]', text.replace('\ufeff', ''))
    parts = re.split(r"(\n+|(?<=[.!?。！？]) +)", clean)
    return ''.join('[건강정보]' if HEALTH.search(part) else part for part in parts).strip()


def event_fields(text):
    if not text:
        return NULL, NULL
    patterns = (
        ('할인', r'할인|쿠폰|할인가|특가|페이백|\bdiscount\b|割引|折扣'),
        ('리뉴얼', r'리뉴얼\s*(?:행사|이벤트|기념)|재개원\s*(?:행사|이벤트|기념)'),
        ('프로모션', r'프로모션|오픈\s*이벤트|증정\s*행사|리뷰\s*이벤트|\bpromotion\b'),
        ('기타', r'이벤트|경품\s*행사'),
    )
    if re.search(r"(?:이벤트|할인)(?:인지|인지는|일지도)|할인\s*(?:같|인 듯)", text):
        return NULL, NULL
    for kind, pattern in patterns:
        if re.search(pattern, text, re.I):
            return 'true', kind
    if re.search(r'리뉴얼|혜택|행사|저렴|서비스로|\bdeal\b', text, re.I):
        return NULL, NULL
    return 'false', NULL


def make_row(hospital, card, occurrences):
    body = (card.get('body') or '').strip()
    score = (card.get('score') or '').strip()
    score = score if re.fullmatch(r'(?:[0-4](?:\.\d+)?|5(?:\.0+)?)', score) else NULL
    displayed = (card.get('date') or '').strip()
    written = review_date(displayed, card.get('machine'))
    if not body and score == NULL and written == NULL:
        raise CollectionError('리뷰 카드에서 본문·날짜·점수를 확인할 수 없음')
    review_id = card.get('id') or ''
    if not re.fullmatch(r'[A-Za-z0-9_-]{1,120}', review_id):
        attrs = [hospital['id'], written, normalized(body), card.get('source') or '']
        key = hashlib.sha256(json.dumps(attrs, ensure_ascii=False).encode('utf-8')).hexdigest()
        occurrences[key] += 1
        review_id = f'local:{key}:{occurrences[key]}'
    mentioned, kind = event_fields(body)
    return dict(zip(FIELDS, (
        review_id, redact(body) or NULL, score, written, language(body), hospital['id'],
        hospital['name'], hospital.get('department', '외과'), hospital.get('address') or NULL,
        hospital.get('official_url') or NULL, str(hospital['total']) if hospital.get('total') is not None else NULL,
        NULL, mentioned, kind, now(),
    ), strict=True))


def inspect_csv(path, department='외과'):
    report = {'path': str(path), 'exists': path.is_file(), 'bytes': 0, 'columns': 0,
              'rows': 0, 'hospital_count': 0, 'duplicate_ids': 0, 'over_40': {},
              'other_department_rows': 0, 'utf8_sig': False, 'problems': []}
    ids, counts = {}, Counter()
    if not report['exists']:
        return report, ids, counts
    data = path.read_bytes()
    report['bytes'] = len(data)
    report['utf8_sig'] = data.startswith(codecs.BOM_UTF8) and data.count(codecs.BOM_UTF8) == 1
    if not report['utf8_sig'] or not data.endswith(b'\n'):
        report['problems'].append('UTF-8 BOM 또는 마지막 행의 줄바꿈 오류')
    try:
        with path.open('r', encoding='utf-8-sig', newline='') as source:
            reader = csv.reader(source, strict=True)
            header = next(reader, [])
            report['columns'] = len(header)
            if tuple(header) != FIELDS:
                report['problems'].append('헤더 또는 열 순서 오류')
            for row in reader:
                report['rows'] += 1
                if len(row) != len(FIELDS) or not all(row) or row == list(FIELDS):
                    report['problems'].append(f'행 형식 오류 {reader.line_num}')
                    continue
                rid, hospital_id = row[0], row[5]
                if rid == NULL or hospital_id == NULL:
                    report['problems'].append(f'필수 ID 결측 {reader.line_num}')
                report['duplicate_ids'] += rid in ids
                ids[rid] = hospital_id
                counts[hospital_id] += 1
                report['other_department_rows'] += row[7] != department
    except (UnicodeError, csv.Error) as exc:
        report['problems'].append(f'CSV 읽기 오류 ({type(exc).__name__})')
    report['hospital_count'] = len(counts)
    report['over_40'] = {hid: n for hid, n in counts.items() if n > MAX_REVIEWS}
    if any(report[k] for k in ('over_40', 'duplicate_ids', 'other_department_rows')):
        report['problems'].append('병원당 상한, 리뷰 ID 중복 또는 대상 진료과 검증 실패')
    return report, ids, counts


def retry_file_operation(operation, description):
    for attempt in range(10):
        try:
            return operation()
        except PermissionError as exc:
            if attempt == 9:
                raise CollectionError(f'{description} 권한 오류: {exc}') from exc
            time.sleep(0.05 * (attempt + 1))


class CsvStore:
    def __init__(self, path, department='외과'):
        self.path = path
        self.department = department
        report, self.ids, self.counts = inspect_csv(path, department)
        if report['problems']:
            raise CollectionError(str(report['problems']))
        self.file = None

    def add(self, row):
        rid, hospital_id = row['review_id'], row['hospital_id']
        if rid in self.ids:
            if self.ids[rid] != hospital_id:
                raise CollectionError('서로 다른 병원에서 동일한 공개 리뷰 ID 발견')
            return
        if self.counts[hospital_id] >= MAX_REVIEWS:
            return
        if self.file is None:
            new = not self.path.exists()
            self.file = retry_file_operation(
                lambda: self.path.open('x' if new else 'a', newline='', encoding='utf-8-sig' if new else 'utf-8'),
                'CSV 열기',
            )
            self.writer = csv.DictWriter(self.file, fieldnames=FIELDS)
            if new:
                self.writer.writeheader()
        first = not self.ids
        self.writer.writerow(row)
        # close() can persist this buffered row even when this flush fails.
        # Remember it before flushing so a retry in the same run cannot append it twice.
        self.ids[rid] = hospital_id
        self.counts[hospital_id] += 1
        retry_file_operation(self.file.flush, 'CSV 행 플러시')
        if first:
            self.sync()
            report, _, _ = inspect_csv(self.path, self.department)
            if report['problems'] or report['rows'] != 1 or report['bytes'] <= 0:
                raise CollectionError('최초 저장 행 다시 읽기 검증 실패')
            LOG.info('최초 저장 검증 %s bytes=%d columns=%d rows=1', self.path, report['bytes'], report['columns'])

    def sync(self):
        if self.file is not None:
            retry_file_operation(self.file.flush, 'CSV 병원 종료 플러시')
            retry_file_operation(lambda: os.fsync(self.file.fileno()), 'CSV fsync')

    def close(self):
        if self.file is not None:
            try:
                self.sync()
            finally:
                try:
                    self.file.close()
                finally:
                    self.file = None


@contextmanager
def single_run(root):
    name = hashlib.sha256(str(root.resolve()).casefold().encode()).hexdigest()[:24]
    lock_path = Path(tempfile.gettempdir()) / f'reviewed-surgery-{name}.lock'
    with lock_path.open('a+b') as handle:
        handle.seek(0)
        try:
            if os.name == 'nt':
                import msvcrt
                msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as exc:
            raise CollectionError('같은 작업공간에서 수집기가 이미 실행 중 또는 잠금 실패') from exc
        yield


class Checkpoint:
    def __init__(self, path):
        self.path = path
        self.state = {'status': 'pending', 'reported_total': None, 'listing_complete': False,
                      'hospitals': {}, 'results': {}, 'sample_ids': [], 'sample_done': False,
                      'last_completed_hospital': None, 'current_hospital': None, 'reason': None}
        if path.exists():
            self.state.update(json.loads(path.read_text(encoding='utf-8')))

    def save(self, **updated):
        self.state.update(updated, updated_at=now())
        pending = self.path.with_suffix('.json.tmp')
        with pending.open('w', encoding='utf-8', newline='\n') as file:
            json.dump(self.state, file, ensure_ascii=False, indent=2)
            file.write('\n')
            file.flush()
            os.fsync(file.fileno())
        # Windows readers can briefly deny replacing an open destination.
        retry_file_operation(lambda: pending.replace(self.path), '체크포인트 교체')


NEW_LIST_CARDS = r"""(links, afterUrl) => {
    const offset = afterUrl ? links.findIndex(link => link.href === afterUrl) + 1 : 0;
    if (afterUrl && !offset) return [];
    return links.slice(offset).filter(link => link.getClientRects().length
        && getComputedStyle(link).visibility !== 'hidden');
}"""

LIST_CARDS = r"""(links, afterUrl) => (""" + NEW_LIST_CARDS + r""")(links, afterUrl).map(link => {
    const info = link.querySelector('.search-hospital-text');
    const meta = info?.querySelector('p');
    const divider = meta?.querySelector('.search-hospital-divider');
    const after = [];
    for (let node = divider?.nextSibling; node; node = node.nextSibling) {
        after.push(node.nodeType === Node.TEXT_NODE ? node.nodeValue : node.innerText || '');
    }
    return {url: link.href, name: info?.querySelector('h2')?.innerText.trim(),
            department: after.join(' ').trim()};
})"""

DETAIL_METADATA = r"""() => {
    const shown = e => !!e?.getClientRects().length && getComputedStyle(e).visibility !== 'hidden';
    const meta = document.querySelector('.detail-name-meta');
    const divider = meta?.querySelector('.detail-divider');
    const links = [...document.querySelectorAll('a[href]')].filter(a => shown(a)
        && /^(?:병원\s*|공식\s*)?(?:홈페이지|웹사이트)(?:\s*(?:바로가기|보기))?$/.test(a.innerText.trim())
        && a.origin !== location.origin && /^https?:$/.test(a.protocol));
    return {name: document.querySelector('.detail-name h1')?.innerText.trim(),
        department: divider?.nextElementSibling?.innerText.trim(),
        address: document.querySelector('.detail-address > span')?.innerText.trim(),
        count: document.querySelector('.detail-reviews h2')?.innerText.trim(),
        heroCount: meta?.innerText.match(/리뷰\s*[\d,]+/)?.[0],
        website: links.length === 1 ? links[0].href : null};
}"""

REVIEW_CARDS = r"""(rows, range) => rows.slice(range[0], range[1]).map(row => {
    const body = row.querySelector('.detail-review-copy');
    const time = row.querySelector('time');
    const channel = row.querySelector('.detail-review-meta > span:first-child [aria-label]');
    const rating = row.querySelector('.detail-review-rating strong');
    return {body: body?.innerText.trim(), date: time?.innerText.trim(),
        machine: time?.getAttribute('datetime'), source: channel?.getAttribute('aria-label'),
        score: rating?.innerText.trim(), id: row.getAttribute('data-review-id')
            || row.id.match(/^review[-_:](\w[\w-]*)$/)?.[1]};
})"""


class Browser:
    def __init__(self, page, interval, department, start_url):
        self.page = page
        self.interval = interval
        self.department = department
        self.start_url = start_url
        self.last_action = float('-inf')
        self.stop = None
        self.robots = None
        page.on('response', self.check_response)

    def check_response(self, response):
        if urlsplit(response.url).netloc != 'reviewed.co.kr':
            return
        # Use the server's status/Retry-After only. No response payload or endpoint discovery.
        retry = response.headers.get('retry-after')
        if response.status in (403, 429) or retry:
            self.stop = f'리뷰드 HTTP {response.status}' + (f', Retry-After {retry}' if retry else '')

    def check_access(self):
        if self.stop:
            raise AccessStop(self.stop)
        block = self.page.get_by_text(re.compile(
            r'^(?:접근이 제한되었습니다|보안 확인이 필요합니다|Verify you are human|Just a moment\.\.\.)$', re.I))
        challenge = self.page.locator('iframe[title*="captcha" i]:visible, iframe[title*="challenge" i]:visible')
        if challenge.count() or block.first.is_visible():
            raise AccessStop('접근 제한 또는 CAPTCHA 확인')

    def pace(self):
        self.check_access()
        time.sleep(max(0, self.last_action + self.interval - time.monotonic()))
        self.check_access()
        self.last_action = time.monotonic()

    def open(self, url):
        domain = urlsplit(url).netloc
        if domain == 'reviewed.co.kr' and self.robots and not self.robots.can_fetch('*', url):
            raise AccessStop('robots.txt에서 화면 접근을 허용하지 않음')
        self.pace()
        response = self.page.goto(url, wait_until='domcontentloaded', timeout=25000)
        self.check_access()
        if response is None or not response.ok:
            status = response.status if response else '응답 없음'
            raise CollectionError(f'공개 페이지 로드 실패 {status}')
        return response

    def click(self, control):
        self.pace()
        control.click(timeout=12000)
        self.check_access()

    def preflight(self):
        self.open(f'{ORIGIN}/robots.txt')
        rules = self.page.locator('body').inner_text(timeout=3000)
        if not re.search(r'^\s*User-agent\s*:', rules, re.M | re.I):
            raise AccessStop('robots.txt 공개 규칙을 확인할 수 없음')
        self.robots = RobotFileParser()
        self.robots.parse(rules.splitlines())
        for url in (self.start_url, f'{ORIGIN}/ko/hospital/', f'{ORIGIN}/ko/review-detail/'):
            if not self.robots.can_fetch('*', url):
                raise AccessStop('robots.txt에서 대상 공개 화면을 허용하지 않음')
        delay = self.robots.crawl_delay('*') or 0
        rate = self.robots.request_rate('*')
        self.interval = max(self.interval, delay, rate.seconds / rate.requests if rate else 0)
        LOG.info('robots.txt 검사 통과, 브라우저 작업 간격 %.2f초', self.interval)

    def list_page(self):
        self.open(self.start_url)
        total = self.search_total()
        filter_label = self.page.get_by_text(self.department, exact=True)
        if not filter_label.first.is_visible() and not self.page.locator(HOSPITAL_LINKS).count():
            raise CollectionError(f'{self.department} 검색 결과 필터 표시 확인 실패')
        if self.page.url != self.start_url:
            raise CollectionError(f'지정한 {self.department} 전국 검색 URL이 변경됨')
        return total

    def search_total(self):
        total = self.page.get_by_text(re.compile(r'^\s*\d[\d,]*개의 검색 결과\s*$')).first
        total.wait_for(state='visible', timeout=12000)
        return count_from(total.inner_text())

    def visible_hospitals(self, after_url=None):
        hospitals = {}
        for card in self.page.locator('a:has(.search-hospital-text)').evaluate_all(LIST_CARDS, after_url):
            if card['department'] != self.department:
                raise CollectionError(f'목록 카드의 정확한 {self.department} 표시를 확인할 수 없음')
            match = re.fullmatch(r'https://reviewed\.co\.kr/ko/hospital/(\d+)/?', card['url'])
            if not match or not card['name']:
                raise CollectionError('공개 카드의 병원 ID 또는 병원명 확인 실패')
            hospitals[match[1]] = {'id': match[1], 'name': card['name'], 'url': card['url']}
        return hospitals

    def listing(self, checkpoint):
        target = self.list_page()
        earlier = checkpoint.state['hospitals'] if checkpoint.state['reported_total'] == target else {}
        confirmed = earlier.copy()
        checkpoint.save(reported_total=target, hospitals=confirmed, listing_complete=False)
        cards = self.expand_listing(checkpoint, target, confirmed)
        checkpoint.save(hospitals=cards, listing_complete=True)
        LOG.info('병원 목록 끝 확인 %d곳', len(cards))
        return cards

    def expand_listing(self, checkpoint, target, confirmed, region=None):
        more = self.page.locator(LIST_MORE)
        cards = self.visible_hospitals()
        if not cards:
            raise CollectionError('내역을 시작할 공개 병원 카드가 표시되지 않음')
        confirmed.update(cards)
        scope = f' [{region}]' if region else ''
        LOG.info('목록 시작%s %d/%d곳', scope, len(cards), target)
        try:
            while more.is_visible():
                before = len(cards)
                tail = cards[next(reversed(cards))]['url']
                self.click(more)
                try:
                    self.page.wait_for_function(
                        "(afterUrl) => (" + NEW_LIST_CARDS
                        + ")(Array.from(document.querySelectorAll('a:has(.search-hospital-text)')), afterUrl).length > 0",
                        arg=tail, timeout=18000,
                    ).dispose()
                except self.timeout_error:
                    self.check_access()
                    raise CollectionError(f'병원 더보기 후 다음 카드가 표시되지 않음 ({before}/{target}곳)') from None
                added = self.visible_hospitals(after_url=tail)
                cards.update(added)
                confirmed.update(added)
                if len(cards) <= before:
                    raise CollectionError('병원 더보기 이후 고유 병원 수 증가 확인 실패')
                if len(cards) // 25 > before // 25:
                    checkpoint.save(hospitals=confirmed)
                if len(cards) // 100 > before // 100:
                    LOG.info('목록 진행%s %d/%d곳', scope, len(cards), target)
        finally:
            checkpoint.save(hospitals=confirmed)
        if len(cards) != target:
            raise CollectionError(f'병원 더보기 종료{scope} 후 화면의 전체 {target}곳과 고유 목록 {len(cards)}곳 불일치')
        return cards

    def region_dialog(self):
        self.click(self.page.get_by_role('button', name='지역', exact=True))
        modal = self.page.locator('[class*="RegionSelectionModal-"][class*="__dialog"]:visible')
        modal.wait_for(state='visible', timeout=12000)
        return modal

    def regional_listing(self, checkpoint):
        target = self.list_page()
        modal = self.region_dialog()
        groups = [label for label in modal.locator('button:visible').all_inner_texts()
                  if label not in ('', '초기화', '완료')]
        if not groups or len(groups) != len(set(groups)):
            raise CollectionError('공개 지역 필터의 전체 지역을 확인할 수 없음')
        state = checkpoint.state
        progress = state.get('region_listings', {})
        confirmed = state['hospitals'].copy()
        checkpoint.save(reported_total=target, listing_mode='regional', listing_complete=False,
                        region_groups=groups, region_listings=progress, hospitals=confirmed)
        for region in groups:
            if region in progress:
                continue
            self.list_page()
            modal = self.region_dialog()
            self.click(modal.get_by_role('button', name=region, exact=True))
            checkbox = modal.get_by_role('checkbox', name=f'{region} 전체', exact=True)
            self.click(checkbox)
            if not checkbox.is_checked():
                raise CollectionError(f'지역 전체 옵션을 선택할 수 없음 [{region}]')
            self.click(modal.get_by_role('button', name='완료', exact=True))
            self.page.wait_for_url(lambda url: url != self.start_url, timeout=12000)
            self.page.get_by_role('button', name=f'{region} 전체', exact=True).wait_for(
                state='visible', timeout=12000)
            self.page.locator(HOSPITAL_LINKS).first.wait_for(state='visible', timeout=25000)
            count = self.search_total()
            checkpoint.save(listing_region=region)
            region_cards = self.expand_listing(checkpoint, count, confirmed, region)
            progress[region] = {'count': count, 'hospital_ids': list(region_cards)}
            checkpoint.save(region_listings=progress, listing_region=None, hospitals=confirmed)
            LOG.info('지역 목록 완료 [%s] %d곳, 전국 확인 누계 %d/%d곳', region, count, len(confirmed), target)
        regional_ids = {hid for region in groups for hid in progress[region]['hospital_ids']}
        listed_total = sum(progress[region]['count'] for region in groups)
        cards = {hid: hospital for hid, hospital in confirmed.items() if hid in regional_ids}
        if len(cards) != target or len(regional_ids) != target or listed_total != target:
            raise CollectionError(f'전국 표시 {target}곳, 지역 합계 {listed_total}곳, '
                                  f'지역 고유 병원 {len(regional_ids)}곳, 확인한 병원 {len(cards)}곳 불일치')
        checkpoint.save(hospitals=cards, listing_complete=True, listing_region=None)
        LOG.info('병원 목록 끝 확인 %d곳 (공개 지역 %d개, 지역 검색 고유 %d곳)', len(cards), len(groups), len(regional_ids))
        return cards

    def official_site(self, candidate, hospital, address):
        if not candidate or not address:
            return None
        try:
            self.open(candidate)
            body = self.page.locator('body').inner_text(timeout=6000)
            compact = lambda value: re.sub(r'[^\w]', '', value).casefold()
            road = re.search(r'\S+(?:로|길)\s+\d+(?:-\d+)?', address)
            if road and compact(hospital['name']) in compact(body) and compact(road[0]) in compact(body):
                return self.page.url
        except AccessStop:
            raise
        except (CollectionError, self.timeout_error):
            LOG.info('병원 %s 홈페이지 확인 불가', hospital['id'])
        return None

    def collect_hospital(self, hospital, store, limit):
        self.open(hospital['url'])
        self.page.locator('.detail-name h1:visible').wait_for(timeout=10000)
        info = self.page.evaluate(DETAIL_METADATA)
        if not info['name'] or normalized(info['name']) != normalized(hospital['name']):
            raise CollectionError('상세 화면의 병원명이 목록과 다름')
        if info['department'] and info['department'] != self.department:
            raise CollectionError(f'상세 화면 진료과가 정확히 {self.department}로 표시되지 않음')
        hospital = hospital | {'name': info['name'], 'address': info['address'],
                               'total': count_from(info['count'] or info['heroCount']),
                               'department': self.department}
        if info['website'] and info['address']:
            hospital['official_url'] = self.official_site(info['website'], hospital, info['address'])
            self.open(hospital['url'])
            self.page.locator('.detail-name h1:visible').wait_for(timeout=10000)
        rows = self.page.locator(ROW_SELECTOR)
        total = hospital['total']
        if not rows.count() and total != 0:
            rows.first.wait_for(state='visible', timeout=12000)
        scanned = self.save_rows(rows, 0, limit, hospital, store, Counter())
        if scanned >= limit or store.counts[hospital['id']] >= limit:
            return
        link = self.page.locator('.detail-reviews a.detail-more:visible')
        if link.is_visible():
            self.click(link)
            self.page.wait_for_url(re.compile(r'/ko/review-detail/\d+(?:[/?#]|$)'), timeout=12000)
            rows.first.wait_for(state='visible', timeout=12000)
            # The expanded page starts its list at the first review again.
            scanned = 0
        elif total is not None and scanned < min(total, limit):
            raise CollectionError('표시된 리뷰 수보다 적으며 더보기 링크가 없음')
        else:
            return
        more = self.page.locator('.detail-reviews button.detail-more:visible')
        occurrences = Counter()
        while True:
            scanned = self.save_rows(rows, scanned, limit, hospital, store, occurrences)
            if scanned >= limit or store.counts[hospital['id']] >= limit:
                return
            if not more.is_visible():
                if total is not None and scanned < min(total, limit):
                    raise CollectionError('더보기 종료 후 표시된 리뷰 수와 불일치')
                return
            self.click(more)
            rows.nth(scanned).wait_for(state='visible', timeout=12000)

    def save_rows(self, rows, start, limit, hospital, store, occurrences):
        self.check_access()
        cards = rows.evaluate_all(REVIEW_CARDS, [start, limit])
        for card in cards:
            if store.counts[hospital['id']] >= limit:
                break
            store.add(make_row(hospital, card, occurrences))
        return start + len(cards)


def run_hospital(browser, hospital, store, checkpoint, limit):
    hid = hospital['id']
    checkpoint.save(current_hospital=hid)
    done = False
    reason = None
    try:
        if store.counts[hid] < limit:
            browser.collect_hospital(hospital, store, limit)
        done = True
    except (AccessStop, KeyboardInterrupt):
        reason = browser.stop or '접근 제한 또는 중단'
        raise
    except CollectionError as exc:
        reason = str(exc)
    except browser.timeout_error:
        browser.check_access()
        reason = '공개 화면 또는 더보기 로딩 시간 초과'
    except browser.playwright_error:
        browser.check_access()
        reason = '브라우저 페이지 이동 또는 DOM 오류'
        if browser.page.is_closed():
            raise CollectionError(reason)
    finally:
        store.close()
        results = checkpoint.state['results']
        status = 'complete' if done and limit == MAX_REVIEWS else 'sample' if done else 'incomplete'
        results[hid] = {'name': hospital['name'], 'status': status, 'rows': store.counts[hid], 'reason': reason}
        checkpoint.save(current_hospital=None if done else hid,
                        last_completed_hospital=hid if status == 'complete' else checkpoint.state['last_completed_hospital'])
        LOG.info('병원 %s %s %s 저장=%d 누적=%d%s', hid, hospital['name'], status,
                 store.counts[hid], len(store.ids), f' 사유={reason}' if reason else '')
    return done


def report_run(path, checkpoint, department='외과'):
    report, _, counts = inspect_csv(path, department)
    state = checkpoint.state
    report.update(status=state['status'], displayed_target=state['reported_total'],
                  enumerated=len(state['hospitals']), listing_complete=state['listing_complete'],
                  completed=sum(x['status'] == 'complete' for x in state['results'].values()),
                  failures={k: v['reason'] for k, v in state['results'].items() if v['status'] == 'incomplete'},
                  reason=state['reason'])
    count_message = dict(report)
    count_message['failure_count'] = len(count_message.pop('failures'))
    LOG.info('검증 %s', json.dumps(count_message, ensure_ascii=False))
    return report, counts


def run(args, path, checkpoint, start_url):
    from playwright.sync_api import Error, TimeoutError, sync_playwright

    state = checkpoint.state
    store = CsvStore(path, args.department)
    if any(store.counts[hid] < result['rows'] for hid, result in state['results'].items()):
        raise CollectionError('체크포인트의 저장 건수보다 CSV 행이 적음. 기존 파일을 확인해야 함')
    if not args.preflight_only:
        checkpoint.save(status='running', reason=None)
    try:
        with sync_playwright() as playwright:
            with playwright.chromium.launch(channel=args.channel, headless=True) as chrome:
                page = chrome.new_page(locale='ko-KR', viewport={'width': 1280, 'height': 900})
                browser = Browser(page, args.interval, args.department, start_url)
                browser.timeout_error = TimeoutError
                browser.playwright_error = Error
                browser.preflight()
                if args.preflight_only:
                    return 0
                if not state['sample_done']:
                    sample_ids = state['sample_ids']
                    if not sample_ids:
                        target = browser.list_page()
                        sample = dict(list(browser.visible_hospitals().items())[:2])
                        if len(sample) < 2:
                            raise CollectionError('표본을 수집할 공개 대상 병원이 2곳 미만')
                        sample_ids = list(sample)
                        checkpoint.save(reported_total=target, hospitals=sample, sample_ids=sample_ids)
                    for hid in sample_ids:
                        if not run_hospital(browser, state['hospitals'][hid], store, checkpoint, 5):
                            raise CollectionError('표본 병원 처리 실패')
                    sample_report, counts = report_run(path, checkpoint, args.department)
                    if sample_report['problems'] or any(not 1 <= counts[hid] <= 5 for hid in sample_ids):
                        raise CollectionError('실제 병원 2곳 CSV 표본 검증 실패')
                    checkpoint.save(sample_done=True)
                    LOG.info('실제 표본 검증 통과 %s', {hid: counts[hid] for hid in sample_ids})
                if args.sample_only:
                    checkpoint.save(status='sample_complete')
                    return 0
                if not state['listing_complete'] and len(state['hospitals']) > 2:
                    current_total = browser.list_page()
                    if current_total == state['reported_total']:
                        previously_seen = [
                            h for hid, h in state['hospitals'].items()
                            if state['results'].get(hid, {}).get('status') != 'complete'
                        ][:25]
                        for hospital in previously_seen:
                            run_hospital(browser, hospital, store, checkpoint, MAX_REVIEWS)
                if state['listing_complete']:
                    hospitals = state['hospitals']
                elif args.by_region or state.get('listing_mode') == 'regional':
                    hospitals = browser.regional_listing(checkpoint)
                else:
                    hospitals = browser.listing(checkpoint)
                for attempt in range(2):
                    pending = [hid for hid in hospitals if state['results'].get(hid, {}).get('status') != 'complete']
                    if not pending:
                        break
                    if attempt:
                        LOG.info('일시 오류로 미완료된 병원 %d곳 재시도', len(pending))
                    for hid in pending:
                        run_hospital(browser, hospitals[hid], store, checkpoint, MAX_REVIEWS)
                missing = [hid for hid in hospitals if state['results'].get(hid, {}).get('status') != 'complete']
                checked, counts = report_run(path, checkpoint, args.department)
                unexpected = set(counts) - set(hospitals)
                count_mismatches = [
                    hid for hid in hospitals if state['results'].get(hid, {}).get('status') == 'complete'
                    and state['results'][hid]['rows'] != counts[hid]
                ]
                if missing or unexpected or count_mismatches or checked['problems'] or not checked['rows']:
                    raise CollectionError(f'전국 검증 미완료: 미완료 병원 {len(missing)}곳, '
                                          f'현재 목록에 없는 저장 병원 {len(unexpected)}곳, '
                                          f'병원별 건수 불일치 {len(count_mismatches)}곳, CSV 오류 {checked["problems"]}')
                checkpoint.save(status='complete', current_hospital=None)
                return 0
    except (AccessStop, CollectionError, KeyboardInterrupt, Error, OSError) as exc:
        reason = str(exc) if isinstance(exc, (CollectionError, OSError)) else (
            '사용자 또는 실행 환경에서 중단' if isinstance(exc, KeyboardInterrupt) else f'Playwright {type(exc).__name__}')
        if not args.preflight_only:
            checkpoint.save(status='incomplete', reason=reason)
        LOG.error('%s', reason)
        if isinstance(exc, Error):
            LOG.debug('Playwright 오류 요약 %s', str(exc).splitlines()[0])
        return 1
    finally:
        store.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--verify', action='store_true', help='CSV 및 체크포인트만 읽어서 검증')
    mode.add_argument('--preflight-only', action='store_true', help='브라우저와 robots.txt 확인')
    mode.add_argument('--sample-only', action='store_true', help='기존 데이터와 연결되는 2곳 표본 검증만 실행')
    parser.add_argument('--channel', default='msedge', help='설치된 Chromium 채널, 예 msedge 또는 chrome')
    parser.add_argument('--department', choices=DEPARTMENTS, default='외과', help='전국 검색의 진료과')
    parser.add_argument('--by-region', action='store_true', help='공개 지역 필터를 순회해 전국 목록을 확인')
    parser.add_argument('--interval', type=float, default=1.08, help='브라우저 작업 사이 최소 초, 1초 이상')
    parser.add_argument('--local-use-confirmed', action='store_true', help='개인 PC 보관과 해당 이용 범위 확인')
    args = parser.parse_args()
    if not args.interval >= 1 or args.interval == float('inf'):
        parser.error('--interval은 1초 이상 유한한 값이어야 합니다')
    if not (args.verify or args.preflight_only or args.local_use_confirmed):
        parser.error('개인 PC 보관 및 이용 범위 확인 후 --local-use-confirmed를 지정하세요')
    root = Path.cwd().resolve()
    stem, start_url = DEPARTMENTS[args.department]
    path = root / f'{stem}.csv'
    checkpoint_path = root / f'{stem}.checkpoint.json'
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8', errors='backslashreplace')
    log_format = '%(asctime)s %(levelname)s %(message)s'
    # Read-only checks must work while the collector holds the workspace lock.
    handlers = [logging.StreamHandler(sys.stdout)]
    if not args.verify:
        handlers.append(logging.FileHandler(root / f'{stem}.log', encoding='utf-8'))
    logging.Formatter.converter = staticmethod(lambda _: datetime.now(KST).timetuple())
    logging.basicConfig(level=logging.INFO, format=log_format, handlers=handlers)
    try:
        if args.verify:
            checkpoint = Checkpoint(checkpoint_path)
            report, counts = report_run(path, checkpoint, args.department)
            print(json.dumps(report | {'rows_by_hospital': counts}, ensure_ascii=False))
            return 1 if not report['exists'] or report['problems'] else 0
        with single_run(root):
            checkpoint = Checkpoint(checkpoint_path)
            result = run(args, path, checkpoint, start_url)
            report_run(path, checkpoint, args.department)
            return result
    except (CollectionError, OSError, ImportError, ValueError) as exc:
        LOG.error('%s', exc)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())

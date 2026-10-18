const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const { chromium } = require(process.env.GRAMMAR_PLAYWRIGHT || 'playwright');

(async () => {
  const browser = await chromium.launch({
    headless: true,
    ...(process.env.GRAMMAR_CHROME_PATH ? { executablePath: process.env.GRAMMAR_CHROME_PATH } : {})
  });
  const errors = [];
  const checks = [];
  const base = process.env.GRAMMAR_BASE_URL || 'http://127.0.0.1:8765';
  const artifacts = path.resolve('ui_artifacts');
  fs.mkdirSync(artifacts, { recursive: true });
  try {
    const page = await browser.newPage({ viewport: { width: 1512, height: 982 }, deviceScaleFactor: 1 });
    page.on('pageerror', error => errors.push(`page: ${error.message}`));
    page.on('console', message => {
      if (message.type() === 'error') errors.push(`console: ${message.text()}`);
    });
    page.on('response', response => {
      if (response.url().includes('/api/') && response.status() >= 400) errors.push(`HTTP ${response.status()}: ${response.url()}`);
    });
    await page.route('**/api/advance', route => {
      errors.push('Unexpected computation request; browser verification must use saved levels.');
      return route.fulfill({ status: 409, contentType: 'application/json', body: JSON.stringify({ error: 'Saved levels only during browser verification.' }) });
    });
    const getJSON = async endpoint => {
      const response = await page.request.get(new URL(endpoint, base).href);
      assert.equal(response.ok(), true, endpoint);
      return response.json();
    };
    const openSession = async grammar => {
      const response = await page.request.post(new URL('/api/session', base).href, { data: { grammar, memory_limit_mb: 2048 } });
      assert.equal(response.ok(), true);
      return response.json();
    };
    const waitLevel = async level => {
      await page.waitForFunction(level => document.querySelector('#current-level').textContent === `Level ${level}`, level);
    };
    const waitCounts = async (union, concat) => {
      await page.waitForFunction(({ union, concat }) =>
        document.querySelector('#union-count').textContent.trim() === String(union) &&
        document.querySelector('#concat-count').textContent.trim() === String(concat),
      { union, concat });
    };
    const waitProof = async panel => {
      await page.waitForFunction(panel => document.querySelectorAll(`${panel} .proof-path`).length === 2, panel);
    };
    const witness = panel => page.locator(`${panel} .proof-witness .token`).allTextContents();
    const settlePaint = () => page.evaluate(() => new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve))));
    const noOverflow = async () => assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth), true);
    const focusPage = () => page.evaluate(() => document.activeElement?.blur());
    const grammarRule = id => page.locator(`#grammar-rules .grammar-rule[data-rule-id="${id}"]`);
    const panelBounds = () => page.evaluate(() => {
      const grammar = document.querySelector('#grammar-rules').closest('.grammar-panel').getBoundingClientRect();
      const findings = document.querySelector('#findings-total').closest('.finding-panel').getBoundingClientRect();
      return { grammar: { left: grammar.left, top: grammar.top, bottom: grammar.bottom }, findings: { left: findings.left, top: findings.top } };
    });
    const assertInspectionAboveApproximation = async () => {
      const layout = await page.evaluate(() => {
        const inspection = document.querySelector('.inspection-grid');
        const approximation = document.querySelector('.approximation-section');
        return {
          documentOrder: Boolean(inspection.compareDocumentPosition(approximation) & Node.DOCUMENT_POSITION_FOLLOWING),
          inspectionBottom: inspection.getBoundingClientRect().bottom,
          approximationTop: approximation.getBoundingClientRect().top
        };
      });
      assert.ok(layout.documentOrder, 'Grammar and Findings must precede Approximation in the document.');
      assert.ok(layout.inspectionBottom <= layout.approximationTop, 'Grammar and Findings must appear above Approximation.');
    };
    const assertGlobalTotal = async state => {
      const level = Number((await page.locator('#current-level').innerText()).match(/\d+/)[0]);
      const snapshot = state.levels.find(item => item.level === level);
      assert.ok(snapshot);
      const expected = Object.values(snapshot.counts).reduce((sum, value) => sum + BigInt(value), 0n).toLocaleString();
      const summary = await page.locator('#approximation-summary').innerText();
      assert.ok(summary.includes(expected), `Global total ${expected} must appear in ${summary}`);
      assert.match(summary, /Σ|∑/);
    };

    const roskind = await openSession('roskind');
    assert.ok(roskind.completed_level >= 5, 'Roskind level 5 must already be cached.');
    await page.goto(base);
    await waitLevel(5);
    await waitCounts(2, 0);
    await waitProof('#union-proof');
    assert.equal(await page.locator('#selected-symbol').count(), 0);
    assert.equal(await page.locator('#symbol-select').count(), 0);
    assert.equal(await page.locator('#sentence-list').count(), 0);
    assert.ok(await page.locator('#level-rail').isVisible());
    assert.ok(await page.locator('#grammar-roskind').isVisible());
    assert.ok(await page.locator('#grammar-expression').isVisible());
    await assertGlobalTotal(roskind);
    assert.deepEqual(await witness('#union-proof'), ['TYPEDEFname', '(', 'TYPEDEFname', ')', ';']);
    const roskindProofText = await page.locator('#union-proof').innerText();
    assert.match(roskindProofText, /P311/);
    assert.match(roskindProofText, /P315/);
    assert.equal(await page.locator('#concat-proof .proof-path').count(), 0);
    assert.equal(await page.locator('#grammar-rules .grammar-rule').count(), 642);
    assert.equal(await page.locator('#findings-total').innerText(), '2 reports');
    await page.waitForFunction(() => [...document.querySelectorAll('#grammar-rules .grammar-rule.union-hit')].map(row => row.dataset.ruleId).join(',') === 'P311,P315,P484,P486');
    assert.deepEqual(await page.locator('#grammar-rules .grammar-rule.union-hit').evaluateAll(rows => rows.map(row => row.dataset.ruleId)), ['P311', 'P315', 'P484', 'P486']);
    assert.equal(await page.locator('#grammar-rules .grammar-rule.concat-hit').count(), 0);
    for (const id of ['P311', 'P315', 'P484', 'P486']) {
      assert.equal(await grammarRule(id).locator('.flag.union').innerText(), '∪');
      const badgeColor = await grammarRule(id).locator('.flag.union').evaluate(node => getComputedStyle(node).color.match(/\d+/g).map(Number));
      assert.ok(badgeColor[0] > badgeColor[1] && badgeColor[0] > badgeColor[2], `${id} union badge must use a red hue.`);
    }
    await grammarRule('P484').locator('.flag.union').click();
    await page.waitForFunction(() => document.querySelector('#union-proof .proof-root')?.textContent === 'function_definition');
    const functionProof = await page.locator('#union-proof').innerText();
    assert.match(functionProof, /P484/);
    assert.match(functionProof, /P486/);
    assert.ok((await witness('#union-proof')).length > 0);
    await grammarRule('P311').locator('.flag.union').click();
    await page.waitForFunction(() => document.querySelector('#union-proof .proof-root')?.textContent === 'member_declaration');
    assert.deepEqual(await witness('#union-proof'), ['TYPEDEFname', '(', 'TYPEDEFname', ')', ';']);
    const desktopPanels = await panelBounds();
    assert.ok(desktopPanels.grammar.left < desktopPanels.findings.left);
    await assertInspectionAboveApproximation();
    assert.ok(await page.getByRole('button', { name: /Paper example/i }).isVisible());
    assert.match(await page.locator('#memory-value').innerText(), /MiB/);
    await noOverflow();
    await page.screenshot({ path: path.join(artifacts, 'grammar-roskind-desktop.png'), fullPage: true });
    checks.push('full-grammar Roskind level 5', 'global approximation total', '642 grammar rules beside 2 findings above Approximation on desktop', 'all four certified union rules have red badges', 'P484 badge selects function_definition evidence', 'P311 badge restores member_declaration evidence', '2 union and zero concatenation findings', 'verified P311/P315 witness', 'paper example action', 'memory monitor');

    await page.locator('#grammar-expression').click();
    await page.waitForFunction(() => document.querySelector('#grammar-expression').getAttribute('aria-pressed') === 'true' && !document.querySelector('#grammar-expression').disabled);
    const expressionState = await getJSON('/api/state');
    assert.equal(expressionState.grammar.id, 'expression');
    if ((await page.locator('#current-level').innerText()) !== 'Level 4') {
      await page.locator('#level-rail button[aria-label^="Level 4;"]').click();
    }
    await waitLevel(4);
    await waitCounts(1, 1);
    await waitProof('#union-proof');
    await waitProof('#concat-proof');
    assert.ok(expressionState.completed_level >= 4, 'The paper example must already have saved level 4.');
    await assertGlobalTotal(expressionState);
    assert.deepEqual(await witness('#union-proof'), ['n', '+', 'n', '*', 'n']);
    assert.deepEqual(await witness('#concat-proof'), ['n', '+', 'n', '+', 'n']);
    const expressionProofText = await page.locator('#union-proof').innerText();
    assert.match(expressionProofText, /P001/);
    assert.match(expressionProofText, /P002/);
    assert.equal(await page.locator('#grammar-rules .grammar-rule').count(), 5);
    assert.equal(await page.locator('#findings-total').innerText(), '2 reports');
    assert.equal(await grammarRule('P001').evaluate(row => row.classList.contains('both-hit') && row.classList.contains('union-hit') && row.classList.contains('concat-hit')), true);
    assert.deepEqual(await grammarRule('P001').locator('.flag').allTextContents(), ['∪', '·']);
    assert.equal(await grammarRule('P002').evaluate(row => row.classList.contains('union-hit') && !row.classList.contains('concat-hit') && !row.classList.contains('both-hit')), true);
    assert.deepEqual(await grammarRule('P002').locator('.flag').allTextContents(), ['∪']);
    for (const id of ['P003', 'P004', 'P005']) assert.equal(await grammarRule(id).locator('.flag').count(), 0);
    const splitRows = page.locator('#concat-proof .proof-path .derivation-step').filter({ hasText: '│' });
    assert.equal(await splitRows.count(), 2);
    const renderedSplits = (await splitRows.allTextContents()).map(text => text.replace(/\s+/g, ' ').replace(/\s*│\s*/g, ' │ ').trim());
    assert.deepEqual(renderedSplits, ['n + │ n + n', 'n + n + │ n']);
    const expressionFindings = await getJSON('/api/findings?level=4&limit=50');
    const concatRecord = expressionFindings.items.find(item => item.kind === 'concatenation');
    assert.ok(concatRecord);
    const concatProof = await getJSON(`/api/proof?id=${encodeURIComponent(concatRecord.id)}`);
    assert.equal(concatProof.verified, true);
    assert.deepEqual(concatProof.factorizations.map(item => item.cut), [2, 4]);
    await page.screenshot({ path: path.join(artifacts, 'grammar-paper-both-ambiguities.png'), fullPage: true });
    checks.push('paper grammar switch', 'five paper rules with exact union and concatenation badges', 'supporting rules are not marked as ambiguity sites', 'real union and concatenation witnesses', 'distinct token cuts 2 and 4');

    await focusPage();
    await page.keyboard.press('ArrowLeft');
    await waitLevel(3);
    await waitCounts(0, 0);
    assert.equal(await page.locator('#union-proof .proof-path').count(), 0);
    assert.equal(await page.locator('#concat-proof .proof-path').count(), 0);
    assert.equal(await page.locator('#grammar-rules .grammar-rule.union-hit, #grammar-rules .grammar-rule.concat-hit').count(), 0);
    await page.keyboard.press('ArrowRight');
    await waitLevel(4);
    await waitCounts(1, 1);
    await waitProof('#union-proof');
    await waitProof('#concat-proof');
    assert.deepEqual(await witness('#union-proof'), ['n', '+', 'n', '*', 'n']);
    assert.deepEqual(await witness('#concat-proof'), ['n', '+', 'n', '+', 'n']);
    checks.push('saved level 3 has no findings', 'saved level 4 restores both proofs');

    await page.locator('#level-rail .level-step').first().click();
    await waitLevel(0);
    await waitCounts(0, 0);
    assert.match(await page.locator('#recurrence').innerText(), /L₀\(A\) = ∅/);
    assert.match(await page.locator('#approximation-summary').innerText(), /\b0\b/);
    await page.locator('#level-rail button[aria-label^="Level 4;"]').click();
    await waitLevel(4);
    await waitCounts(1, 1);
    await waitProof('#union-proof');
    await waitProof('#concat-proof');
    checks.push('level 0 begins with empty languages');

    await page.setViewportSize({ width: 390, height: 844 });
    await settlePaint();
    await noOverflow();
    assert.ok(await page.locator('#union-proof').isVisible());
    assert.ok(await page.locator('#concat-proof').isVisible());
    const paperMobilePanels = await panelBounds();
    assert.ok(paperMobilePanels.grammar.top < paperMobilePanels.findings.top);
    assert.ok(paperMobilePanels.grammar.bottom <= paperMobilePanels.findings.top);
    await assertInspectionAboveApproximation();
    await page.screenshot({ path: path.join(artifacts, 'grammar-paper-mobile.png'), fullPage: true });
    await page.locator('#grammar-roskind').click();
    await waitLevel(5);
    await waitCounts(2, 0);
    await waitProof('#union-proof');
    await settlePaint();
    await noOverflow();
    const roskindMobilePanels = await panelBounds();
    assert.ok(roskindMobilePanels.grammar.top < roskindMobilePanels.findings.top);
    assert.ok(roskindMobilePanels.grammar.bottom <= roskindMobilePanels.findings.top);
    await assertInspectionAboveApproximation();
    await page.screenshot({ path: path.join(artifacts, 'grammar-roskind-mobile.png'), fullPage: true });
    checks.push('grammar and findings stack above Approximation at 390 pixels without overflow', 'Roskind restored');

    await openSession('roskind');
    await page.setViewportSize({ width: 1512, height: 982 });
    await page.goto(new URL('/?grammar=roskind&level=5', base).href);
    await waitLevel(5);
    await waitCounts(2, 0);
    await waitProof('#union-proof');
    await settlePaint();
    await noOverflow();
    assert.deepEqual(errors, []);
    console.log(JSON.stringify({ result: 'passed', checks, artifacts, browserErrors: errors }));
  } finally {
    await browser.close();
  }
})().catch(error => { console.error(error); process.exitCode = 1; });

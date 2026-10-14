const fs = require('fs');
const path = require('path');
const { chromium } = require(process.env.OQ7_PLAYWRIGHT || 'playwright');
(async () => {
  const root = path.resolve(__dirname, '..');
  const browser = await chromium.launchPersistentContext(path.join(__dirname,'browser-profile'),{channel:'msedge', headless:true});
  const report = [];
  for (const width of [1440, 390]) {
    const page = await browser.newPage();
    await page.setViewportSize({width,height:1000});
    await page.goto('file:///' + path.join(root,'paper.html').replaceAll('\\','/'));
    await page.screenshot({path:path.join(__dirname,`html-${width}-top.png`)});
    const checks = await page.evaluate(() => {
      const ids = [...document.querySelectorAll('[id]')].map(e=>e.id);
      const links = [...document.querySelectorAll('a[href^="#"]')];
      return {
        title:document.title,
        documentWidth:document.documentElement.scrollWidth,
        viewport:innerWidth,
        equations:document.querySelectorAll('.equation').length,
        mathExpressions:document.querySelectorAll('math').length,
        mathErrors:document.querySelectorAll('merror').length,
        missingLinks:links.map(e=>e.hash.slice(1)).filter(id=>!document.getElementById(id)),
        duplicateIds:ids.filter((v,i)=>ids.indexOf(v)!==i),
        references:document.querySelectorAll('.references li').length,
        figures:document.querySelectorAll('figure').length,
        imagesLoaded:[...document.querySelectorAll('figure img')].every(e=>e.complete&&e.naturalWidth>0),
        overflowingEquationsAccessible:[...document.querySelectorAll('.equation')].filter(e=>e.scrollWidth>e.clientWidth+1).every(e=>e.tabIndex===0&&e.nextElementSibling?.classList.contains('equation-scroll-hint')&&!e.nextElementSibling.hidden),
        equationsWithLocalScroll:[...document.querySelectorAll('.equation')].filter(e=>e.scrollWidth>e.clientWidth+1).map(e=>e.id),
        theoremLabels:[...document.querySelectorAll('.theorem,.lemma,.proposition')].map(e=>({id:e.id,title:e.querySelector('strong').textContent})),
      };
    });
    const targets=['thm:main','fig:geometry','eq:factorization','eq:weyl-blocks','eq:commutator','thm:aperture','eq:electric-inverse','sec:formal','eq:amplitudes-minus','references'];
    for (const id of targets) {
      const el=page.locator(`[id="${id}"]`);
      await el.scrollIntoViewIfNeeded();
      await page.screenshot({path:path.join(__dirname,`html-${width}-${id.replaceAll(':','-')}.png`)});
    }
    report.push({width,...checks});
    if(width===390) {
      const eq=page.locator('[id="eq:main"]');
      await eq.scrollIntoViewIfNeeded();
      await eq.focus();
      const before=await eq.evaluate(e=>e.scrollLeft);
      await page.keyboard.press('End');
      await page.keyboard.press('ArrowRight');
      await page.waitForTimeout(300);
      const after=await eq.evaluate(e=>e.scrollLeft);
      checks.keyboardScrollWorks=after>before;
      await eq.evaluate(e=>e.scrollLeft=e.scrollWidth);
      checks.fullEquationReachable=await eq.evaluate(e=>e.scrollLeft+e.clientWidth>=e.scrollWidth-2);
      report[report.length-1]={width,...checks};
    }
    await page.close();
  }
  await browser.close();
  fs.writeFileSync(path.join(__dirname,'html-render-check.json'),JSON.stringify(report,null,2));
  console.log(JSON.stringify(report,null,2));
  if(report.some(r=>r.documentWidth>r.viewport+1||r.mathErrors||r.missingLinks.length||r.duplicateIds.length||!r.imagesLoaded||!r.overflowingEquationsAccessible||r.keyboardScrollWorks===false||r.fullEquationReachable===false)) process.exitCode=1;
})();

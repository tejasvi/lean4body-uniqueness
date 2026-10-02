module

public import C4Check

public section

/-! Cells `792 ≤ n < 849` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir002

theorem k792_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 792) 2).1
      1600339840325578087508768101012963852081816373280518166443653397015755923251706434383889208054577726870867241045686160357678887486786597621770807582).isSome = true := by
  decide +kernel

theorem k792_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 792) 2).2 2).1
      71767106198769862857978782695797481166288377841060489302626235229753340519961281647355730390191725520327).isSome = true := by
  decide +kernel

theorem k792_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 792) 2).2 2).2
      18375311657889048903649374617317482246269836521823380787058680304587150849852606120468905884573005093770695).isSome = true := by
  decide +kernel

theorem k793_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 793) 2).1
      9448071577657436241170).isSome = true := by
  decide +kernel

theorem k793_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 793) 2).2
      7375643127641004616877054380146910033169307860661417413798139168390607546269295036786928847237806986529738079814221837297008972790613209435693301717560422538499450318).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 794 819 [
    15542003738209344657883226438006882060015798561698972647559413650539634397720336913506, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k819_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 819) 2).1
      5428806006687229647227147420574270044987139776368875936652501602764726952330262327012654729022345808449409534929460720725402695).isSome = true := by
  decide +kernel

theorem k819_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 819) 2).2
      1357496781570625354305570695023482219258518658748057678277997586500210712924085795372369571255342834087446045923636178834429703).isSome = true := by
  decide +kernel

theorem k820_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 820) 2).1 3).1
      249168206566283361492808220755896441011429596091551881717894722177735215672004239112781).isSome = true := by
  decide +kernel

theorem k820_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 820) 2).1 3).2
      3892141753805559844012552057754848608506185843873737417052785123317380703075390347057).isSome = true := by
  decide +kernel

theorem k820_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 820) 2).2
      1639019351604333352292130950644899343456692447381272018968024685436207627957689795191744058364510315746512595894588731672934878346421436987291694910775).isSome = true := by
  decide +kernel

theorem k821_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 821) 2).1
      88776240232807210604488640003355857184926442034445849027754362188031154207638817136279161627202589708043962661094517774050803473607).isSome = true := by
  decide +kernel

theorem k821_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 821) 2).2
      1043578926090058607659129379624672709239496251280405556494578342614493815876908308016338652359).isSome = true := by
  decide +kernel

theorem k822_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 822) 2).1
      73405252640332216314603852624952351396631783353922381120621309859742666091606521269455374039133846710801287).isSome = true := by
  decide +kernel

theorem k822_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 822) 2).2
      15915206188255823326340432278328367982545692751076159220296484693049404926904257693734087).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 823 847 [
    44580606324508122423235773551514773641577734, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k847_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 847) 3).1
      13219939630803615131805049418128600407022991109953471970177341190).isSome = true := by
  decide +kernel

theorem k847_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 847) 3).2
      84955578444970293868604669371313137526526868147948303725695854420362387947229026814307179843775561104928606930533352332640326).isSome = true := by
  decide +kernel

theorem k848_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 848) 3).1 2).1
      243471654377390319864868236188026265373507743562660266136536437045339029893247345009).isSome = true := by
  decide +kernel

theorem k848_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 848) 3).1 2).2
      243519906547045823471825720424268585948084742739393886087857895634766369275644722545).isSome = true := by
  decide +kernel

theorem k848_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 848) 3).2
      355489438025627274206966393339409780799212300148095919488434573860188444678709519314414023973309241585694489817281059081041558396102).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 792 849 :=
  (Cover.one (box := dirCellBox) (n := 792)
      (.split 2 (.leaf _ k792_0) (.split 2 (.leaf _ k792_1) (.leaf _ k792_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 793)
      (.split 2 (.leaf _ k793_0) (.leaf _ k793_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 819)
      (.split 2 (.leaf _ k819_0) (.leaf _ k819_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 820)
      (.split 2 (.split 3 (.leaf _ k820_0) (.leaf _ k820_1)) (.leaf _ k820_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 821)
      (.split 2 (.leaf _ k821_0) (.leaf _ k821_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 822)
      (.split 2 (.leaf _ k822_0) (.leaf _ k822_1))).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 847)
      (.split 3 (.leaf _ k847_0) (.leaf _ k847_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 848)
      (.split 3 (.split 2 (.leaf _ k848_0) (.leaf _ k848_1)) (.leaf _ k848_2)))

end C4.Cert.Dir002

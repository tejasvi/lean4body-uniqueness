module

public import C4Check

public section

/-! Cells `1713 ≤ n < 1743` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir017

theorem k1713_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1713) 3).1
      18209945008133967909951547124680716649170469740033702024799618817096744766124415687338892126247667632966).isSome = true := by
  decide +kernel

theorem k1713_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1713) 3).2
      21436599477004682514419253912075561981311977650353446126448750719415672224489309384500597913011122297339808498080624277116230).isSome = true := by
  decide +kernel

theorem k1714_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1714) 3).1
      100976600516134785759311142011360273121676978804803047788277149457219547050884019338669568446763184188041444284209702736188380986290995917265263858).isSome = true := by
  decide +kernel

theorem k1714_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1714) 3).2 2).1
      289193795178453298650566885718917534928541191924692909247960897745881224496288768995418757465557505135420).isSome = true := by
  decide +kernel

theorem k1714_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1714) 3).2 2).2
      3320230957992796945780870498303646151480094209607789389589893948).isSome = true := by
  decide +kernel

theorem k1715_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1715) 3).1 1).1
      3912363678880590994629372857128303519480015298893917768030614525193528849733065765436).isSome = true := by
  decide +kernel

theorem k1715_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1715) 3).1 1).2
      15651983173294109471230371050299529219668181554409628637559446604636988540058110065724).isSome = true := by
  decide +kernel

theorem k1715_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1715) 3).2 2).1
      977026779564209478676311118665401212491386453228301442904709467377239389838509964348).isSome = true := by
  decide +kernel

theorem k1715_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1715) 3).2 2).2
      977131473253413661365878823554547101469003968526980323121137123092755621518361066556).isSome = true := by
  decide +kernel

theorem k1716_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1716) 3).1
      22284679707398120783365987505674274464357544838614484512325960211562121861700990782010617436475276484113871786620087880215455658226).isSome = true := by
  decide +kernel

theorem k1716_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1716) 3).2
      86981095441788613260770825924918948766173409346311061597261705382217227840196980900325444629146580148721366856567272560727117618).isSome = true := by
  decide +kernel

theorem k1717_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1717) 3).1
      4085454879699796302129561735781739256624377010355888617475581037581007775762168960882872114).isSome = true := by
  decide +kernel

theorem k1717_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1717) 3).2
      1020739332104110033772933226357667234309404320087501729618191760182689335946755998412640050).isSome = true := by
  decide +kernel

theorem k1718_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1718) 3).1
      4595429093127566161964773390955382119872951245495079002725510884165376386896359274712930633929392241062860).isSome = true := by
  decide +kernel

theorem k1718_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1718) 3).2
      248965116159949993936172437339677180485223339744207545033058887295578256701370467899185).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 1719 1720 [
    5549705289769891467806923601930384721936111437143064364322748443406103493320109833329424955085554361818742948217231972539607375053] = true := by
  decide +kernel

theorem c7 : allCells dirCell 1720 1741 [
    3885534434692095802469768237662964208938302642077026504800450317114289121988281851249,
    147508781889523300772, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2844461069167403151098736591449722696376611] = true := by
  decide +kernel

theorem k1741_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1741) 3).1
      15426597311144855281508298769848895429096560607212167030513294129955446882521779570).isSome = true := by
  decide +kernel

theorem k1741_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1741) 3).2
      5359824037579017439732426658915376667831732709112735867076905436942850428821087927750779823037429342729135525129040461474886).isSome = true := by
  decide +kernel

theorem k1742_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1742) 3).1
      101017299716796753173658105767263957337657169824187551231956066973610012138246031035216586175880439626119505640197305794517005359126861418996384754).isSome = true := by
  decide +kernel

theorem k1742_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1742) 3).2
      341543839127647824197556671413200658448583412653584178639184655580293373807644564425979429281190981050918257102775446250550514).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1713 1743 :=
  (Cover.one (box := dirCellBox) (n := 1713)
      (.split 3 (.leaf _ k1713_0) (.leaf _ k1713_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1714)
      (.split 3 (.leaf _ k1714_0) (.split 2 (.leaf _ k1714_1) (.leaf _ k1714_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1715)
      (.split 3 (.split 1 (.leaf _ k1715_0) (.leaf _ k1715_1)) (.split 2 (.leaf _ k1715_2) (.leaf _ k1715_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1716)
      (.split 3 (.leaf _ k1716_0) (.leaf _ k1716_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1717)
      (.split 3 (.leaf _ k1717_0) (.leaf _ k1717_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1718)
      (.split 3 (.leaf _ k1718_0) (.leaf _ k1718_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 1741)
      (.split 3 (.leaf _ k1741_0) (.leaf _ k1741_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1742)
      (.split 3 (.leaf _ k1742_0) (.leaf _ k1742_1)))

end C4.Cert.Dir017

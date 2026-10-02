module

public import C4Check

public section

/-! Cells `3984 ≤ n < 4009` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir134

theorem k3984_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3984) 2).1
      71835970388171860421125831472655419579930351912946691638940677087880235602232663692113311128259622503879).isSome = true := by
  decide +kernel

theorem k3984_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3984) 2).2
      1564595752291612020346089927072293220649627735854486301113340116539687112701140043219596478064406752526742213566396714969597572437500146177897971).isSome = true := by
  decide +kernel

theorem k3985_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3985) 2).1
      15204069149626369984256641567049096161810041951544795793471780140611539915907608947).isSome = true := by
  decide +kernel

theorem k3985_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3985) 2).2
      17950522849435176902060502326370518023806686009506383910265135506624587169823522969963124645218306926023).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 3986 4006 [
    13182958496653226671609764491107239038983503245403238289701433606, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 549763323119386517103532310822810296281024051] = true := by
  decide +kernel

theorem k4006_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).1 2).1 3).1
      64850913116701877467269505278499826270836228873481200348924969929565414256358866289).isSome = true := by
  decide +kernel

theorem k4006_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).1 2).1 3).2
      4111432324212817967829091497280176101413495930191469048865513237414701099346434887049).isSome = true := by
  decide +kernel

theorem k4006_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4006) 3).1 2).2
      22380914527853812385278463104503450848899911905489787718517244134905753083639085001378926370603991100610822152073969675346247).isSome = true := by
  decide +kernel

theorem k4006_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).2 2).1 3).1
      4080972837003360249742863275725467480140083290634173871185083490332694716643861059378).isSome = true := by
  decide +kernel

theorem k4006_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).2 2).1 3).2
      4053563052891803591223360644057683866204402790377386544971472845624005887430395287346).isSome = true := by
  decide +kernel

theorem k4006_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).2 2).2 3).1
      15934674708339685528162569887868825057789669255381133213403170674170706711276737905).isSome = true := by
  decide +kernel

theorem k4006_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).2 2).2 3).2
      4055362016883695165834333623089443225695346563908686857804668933560588299746381731634).isSome = true := by
  decide +kernel

theorem k4007_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).1 2).1
      4016379996701322799650786463195632447021534287409195503280840047036772216926742189873).isSome = true := by
  decide +kernel

theorem k4007_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).1 2).2
      4011051250181886399055471095722540106465741704659344166006556556957756426328181528371).isSome = true := by
  decide +kernel

theorem k4007_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).2 2).1
      3982667873518970500709987387487252299635781542078853054855972085565854130847800514353).isSome = true := by
  decide +kernel

theorem k4007_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).2 2).2
      3985485388149716974302128007972666152276945770600282166847842931948338081803366602545).isSome = true := by
  decide +kernel

theorem k4007_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4007) 2).2 3).1 2).1
      4020705039299264103270394016356608177876077404187082230269378170194944066365477115697).isSome = true := by
  decide +kernel

theorem k4007_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4007) 2).2 3).1 2).2
      872146333400224253369099852287859031547514242042843544775592744753).isSome = true := by
  decide +kernel

theorem k4007_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4007) 2).2 3).2 2).1
      3987859683229191247230261999849267982446472060561486358006434912214634275286434125617).isSome = true := by
  decide +kernel

theorem k4007_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4007) 2).2 3).2 2).2
      865154227798285933414820944014893905410032230413779759823773453105).isSome = true := by
  decide +kernel

theorem k4008_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4008) 2).1 3).1
      1413260166985165187300156226060861849298143394286592011632900638794525722355722577509418673585392407931046950101932646725663612102).isSome = true := by
  decide +kernel

theorem k4008_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4008) 2).1 3).2
      22509606861912755517319165765832396903969747640906410672177101737604319249558168791942720987699248627544659976264355028939764757190).isSome = true := by
  decide +kernel

theorem k4008_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4008) 2).2 3).1
      1631773458153923501570303458249784803538281543658659688739730024205248399816320133487964565296321910663386340375442444057046559837109748348164202290).isSome = true := by
  decide +kernel

theorem k4008_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4008) 2).2 3).2
      6495645937978039550293471371499746309391159861845680254765863958228685418254503188777861008380433078876275946904842097584933781694453653712886259505).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3984 4009 :=
  (Cover.one (box := dirCellBox) (n := 3984)
      (.split 2 (.leaf _ k3984_0) (.leaf _ k3984_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3985)
      (.split 2 (.leaf _ k3985_0) (.leaf _ k3985_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 4006)
      (.split 3 (.split 2 (.split 3 (.leaf _ k4006_0) (.leaf _ k4006_1)) (.leaf _ k4006_2)) (.split 2 (.split 3 (.leaf _ k4006_3) (.leaf _ k4006_4)) (.split 3 (.leaf _ k4006_5) (.leaf _ k4006_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4007)
      (.split 2 (.split 3 (.split 2 (.leaf _ k4007_0) (.leaf _ k4007_1)) (.split 2 (.leaf _ k4007_2) (.leaf _ k4007_3))) (.split 3 (.split 2 (.leaf _ k4007_4) (.leaf _ k4007_5)) (.split 2 (.leaf _ k4007_6) (.leaf _ k4007_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4008)
      (.split 2 (.split 3 (.leaf _ k4008_0) (.leaf _ k4008_1)) (.split 3 (.leaf _ k4008_2) (.leaf _ k4008_3))))

end C4.Cert.Dir134

module

public import C4Check

public section

/-! Cells `3198 ≤ n < 3222` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir095

theorem k3198_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).1 3).1
      15648704404436335595432412550100518572210546800796223726930014585951921010808379134780).isSome = true := by
  decide +kernel

theorem k3198_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).1 3).2
      15637167618837620435219746784343880725209772184684122218682007022199534144826906235708).isSome = true := by
  decide +kernel

theorem k3198_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).2 1).1
      976498419805078076058215208504728553945806557457682509133287546857420860660539323964).isSome = true := by
  decide +kernel

theorem k3198_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).2 1).2
      826971076627286710805303147702890852758445350079751940672429372).isSome = true := by
  decide +kernel

theorem k3198_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3198) 2).2 3).1 1).1
      978538046346982147988900013536161732587581943221989927327827377771841998823644067388).isSome = true := by
  decide +kernel

theorem k3198_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3198) 2).2 3).1 1).2
      212116824167003675677003590625016736105520621334617454625435407164).isSome = true := by
  decide +kernel

theorem k3198_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3198) 2).2 3).2
      474535691884648810968450004162022416578203827293924263443067832266454542673370499878948836968443186150589654969711604817827592370710010228857601900227213416156655635260).isSome = true := by
  decide +kernel

theorem k3199_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3199) 2).1 3).1
      339874572345480319567421603513524047179944665528784030467387429681937224279860319140240835896486793392587314320907024760141041).isSome = true := by
  decide +kernel

theorem k3199_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3199) 2).1 3).2
      5307498298916106628783747117110172205204619590061823080508298432273990929355451499946918877725412508873434123647260552582972).isSome = true := by
  decide +kernel

theorem k3199_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3199) 2).2 3).1
      1360145292390301096962343726461120742846758847060349080727083746927319105267271691899873856050148874120307381928011235099833585).isSome = true := by
  decide +kernel

theorem k3199_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3199) 2).2 3).2
      1151169066465839745162324670040371001168282633706095677679419476502096103840028966847021683735355396672316).isSome = true := by
  decide +kernel

theorem k3200_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3200) 2).1 3).1
      4492586763389730041296820280557593040336151342515838720537935013597484897953061199305817743634616768369).isSome = true := by
  decide +kernel

theorem k3200_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3200) 2).1 3).2
      15214258189138405005475397460297362137866429835637670293924894358617689878260794737).isSome = true := by
  decide +kernel

theorem k3200_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3200) 2).2 3).1
      1150386562567084600991943903097002179375644846028771338868173395095120391537170987116213400111931939834684).isSome = true := by
  decide +kernel

theorem k3200_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3200) 2).2 3).2
      17965691603083036950245388487032748103442719708276742690181990265548182994325195320044621944834020957617).isSome = true := by
  decide +kernel

theorem k3201_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3201) 2).1
      71795729827507122965591650140880094482084438606300178478858155629997505068998811688696039638050873947591).isSome = true := by
  decide +kernel

theorem k3201_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3201) 2).2
      339089454432256955203453264320787995801899773267728073542637708206893144370661365484717715529843433598319458106024499397883123).isSome = true := by
  decide +kernel

theorem k3202_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3202) 2).1
      15197927391338289405761065321981802519187178363131443797815025492670058943096624497).isSome = true := by
  decide +kernel

theorem k3202_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3202) 2).2
      17941695290601502282399675087788793688935412341035954280086389162760901384444776591643806930250426545607).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 3203 3222 [
    13177124224826579081054548691374266756541416182342408691437891846, 9450884999338555175186, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3198 3222 :=
  (Cover.one (box := dirCellBox) (n := 3198)
      (.split 2 (.split 3 (.split 3 (.leaf _ k3198_0) (.leaf _ k3198_1)) (.split 1 (.leaf _ k3198_2) (.leaf _ k3198_3))) (.split 3 (.split 1 (.leaf _ k3198_4) (.leaf _ k3198_5)) (.leaf _ k3198_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3199)
      (.split 2 (.split 3 (.leaf _ k3199_0) (.leaf _ k3199_1)) (.split 3 (.leaf _ k3199_2) (.leaf _ k3199_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3200)
      (.split 2 (.split 3 (.leaf _ k3200_0) (.leaf _ k3200_1)) (.split 3 (.leaf _ k3200_2) (.leaf _ k3200_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3201)
      (.split 2 (.leaf _ k3201_0) (.leaf _ k3201_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3202)
      (.split 2 (.leaf _ k3202_0) (.leaf _ k3202_1))).trans <|
  (Cover.dir c5)

end C4.Cert.Dir095

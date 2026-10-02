module

public import C4Check

public section

/-! Cells `3167 ≤ n < 3168` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir089

theorem k3167_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).1 1).1
      11751238186213379764980479180422330749622284860).isSome = true := by
  decide +kernel

theorem k3167_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).1 1).2
      216586547543438932519877434410595576245592439978179856734816291388).isSome = true := by
  decide +kernel

theorem k3167_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).2
      19235864684570372417376962440907511844057083369975548965951669027969897451672675452959858269099887907754158321).isSome = true := by
  decide +kernel

theorem k3167_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).2 3).1
      1239315620731590375562655766397717739132742167622972833098416490434435386931379148084492818833928196491790764273).isSome = true := by
  decide +kernel

theorem k3167_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).2 3).2
      16706001100309057172062331626518051645086208783490045166075002657648478765709495289526077681).isSome = true := by
  decide +kernel

theorem k3167_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).1 3).1
      88362198312535471037063560103987300872499302172911200493558261799324777250111446834946746161705933532888310338330775774255634673).isSome = true := by
  decide +kernel

theorem k3167_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).1 3).2
      4044626678244892461662213238756867096052438476030964021156845143683219533349267446068465).isSome = true := by
  decide +kernel

theorem k3167_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).2 3).1
      4798658329965554962643422995741723302724959082256950085991972242895250521734591751843379360064759000924145905).isSome = true := by
  decide +kernel

theorem k3167_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).2 3).2
      4782473302340295319106032921905279114594657595893160654352913301685695237398762670274837820536366877802624241).isSome = true := by
  decide +kernel

theorem k3167_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).1 3).1
      77649669888508639893196642230515890112929629579541317120188620646662093133085173708224365668897879012962743100).isSome = true := by
  decide +kernel

theorem k3167_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).1 3).2
      1046095917270132610490603487117232445012712050701623969419335158413100972361875535887200497).isSome = true := by
  decide +kernel

theorem k3167_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).2 1).1
      192563571688449395401393572759910404594392128669939).isSome = true := by
  decide +kernel

theorem k3167_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).2 1).2
      255828748987528932440812009909588915530969117600557301624641896432436391043762774054707).isSome = true := by
  decide +kernel

theorem k3167_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).1 1).1
      16258655003274468485927446356637607399578352931408528696041681846361688747906149178616380).isSome = true := by
  decide +kernel

theorem k3167_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).1 1).2
      16216473890470760914970604100630114708654917517316746736565841471271458749863197777709299).isSome = true := by
  decide +kernel

theorem k3167_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).2 3).1
      260796074184200786968528295310183925280056997628470445585808001193273870325655543361171697).isSome = true := by
  decide +kernel

theorem k3167_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).2 3).2
      1015558246462807965615331599788712535449855992469855925014587212853759948192176536494908).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3167 3168 :=
  (Cover.one (box := dirCellBox) (n := 3167)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3167_0) (.leaf _ k3167_1)) (.leaf _ k3167_2)) (.split 3 (.leaf _ k3167_3) (.leaf _ k3167_4))) (.split 2 (.split 3 (.leaf _ k3167_5) (.leaf _ k3167_6)) (.split 3 (.leaf _ k3167_7) (.leaf _ k3167_8)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3167_9) (.leaf _ k3167_10)) (.split 1 (.leaf _ k3167_11) (.leaf _ k3167_12))) (.split 2 (.split 1 (.leaf _ k3167_13) (.leaf _ k3167_14)) (.split 3 (.leaf _ k3167_15) (.leaf _ k3167_16))))))

end C4.Cert.Dir089

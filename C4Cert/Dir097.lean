module

public import C4Check

public section

/-! Cells `3224 ≤ n < 3227` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir097

theorem k3224_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).1 1).1
      74986772711814940692899489817127988035394792147435329644389910596161674087791628399882089066764199641727804).isSome = true := by
  decide +kernel

theorem k3224_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).1 1).2
      299813654062512858357433185131546372396206617843022754091323770678018098506300590833553289844738346997578812).isSome = true := by
  decide +kernel

theorem k3224_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).2 2).1
      65061994345183699302407994385316220880385650199916213886911942399657042125454483651981553).isSome = true := by
  decide +kernel

theorem k3224_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).2 2).2
      861710246106239580872224864105427220254160218527400037802443141692).isSome = true := by
  decide +kernel

theorem k3224_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).1 1).1
      1011182439790724281155079342980099585713130508644260524305820568638316371402587953626172).isSome = true := by
  decide +kernel

theorem k3224_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).1 1).2
      74594307991698228345717597134110614368213356170442861740552482021522552812487163737721038359707389781146684).isSome = true := by
  decide +kernel

theorem k3224_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).2 2).1
      4047624626239267465282957215310752338414985697663400985513742381128717053831891884768316).isSome = true := by
  decide +kernel

theorem k3224_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).2 2).2
      214390974480851783755988765760859768094275824206888340887386815548).isSome = true := by
  decide +kernel

theorem k3225_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).1 1).1
      251872714574542141279957994423724678888373205264099556730119480959595965892296810232892).isSome = true := by
  decide +kernel

theorem k3225_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).1 1).2
      4028689709095236206890390285072761416272655605389010734185867742814379103177523810005564).isSome = true := by
  decide +kernel

theorem k3225_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).2 1).1
      63033770404233803859485418555118348499684287547825008485110735132788548923741838359612).isSome = true := by
  decide +kernel

theorem k3225_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).2 1).2
      1008123905229976554924076573784937386768132419565018231133636345556410265246959366487100).isSome = true := by
  decide +kernel

theorem k3225_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).1 1).1
      4019102439058946525889989227717881027283419771840749921497763014522569778324718026212156).isSome = true := by
  decide +kernel

theorem k3225_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).1 1).2
      53173705046364219424931641235783186043434950585915983312221237820).isSome = true := by
  decide +kernel

theorem k3225_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).2 1).1
      62850360221802560130076555424197150832223049678496780487115326550997973439790184250428).isSome = true := by
  decide +kernel

theorem k3225_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).2 1).2
      13306613931297016454828362644799782153740355714793100134518979644).isSome = true := by
  decide +kernel

theorem k3226_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3226) 2).1 3).1 1).1
      53074923988209747823344886423607313509766667265200596362331550268).isSome = true := by
  decide +kernel

theorem k3226_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3226) 2).1 3).1 1).2
      212300625650456759702168811270595209813654451418377293300786132540).isSome = true := by
  decide +kernel

theorem k3226_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3226) 2).1 3).2
      1395289448912277078562225476002875337366426937205551270151074372042221598897992328452928881473502544252318216418694641329844859708).isSome = true := by
  decide +kernel

theorem k3226_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3226) 2).2 3).1
      18953296869395534653630174686545254290674963253326250187824478428290631663949389054560524522830720247770587964).isSome = true := by
  decide +kernel

theorem k3226_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3226) 2).2 3).2
      4729770308464499699209663070961299921357595379550200203784658911174607511736440192437597494792877834084590396).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3224 3227 :=
  (Cover.one (box := dirCellBox) (n := 3224)
      (.split 3 (.split 2 (.split 1 (.leaf _ k3224_0) (.leaf _ k3224_1)) (.split 2 (.leaf _ k3224_2) (.leaf _ k3224_3))) (.split 2 (.split 1 (.leaf _ k3224_4) (.leaf _ k3224_5)) (.split 2 (.leaf _ k3224_6) (.leaf _ k3224_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3225)
      (.split 3 (.split 2 (.split 1 (.leaf _ k3225_0) (.leaf _ k3225_1)) (.split 1 (.leaf _ k3225_2) (.leaf _ k3225_3))) (.split 2 (.split 1 (.leaf _ k3225_4) (.leaf _ k3225_5)) (.split 1 (.leaf _ k3225_6) (.leaf _ k3225_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3226)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3226_0) (.leaf _ k3226_1)) (.leaf _ k3226_2)) (.split 3 (.leaf _ k3226_3) (.leaf _ k3226_4))))

end C4.Cert.Dir097

module

public import C4Check

public section

/-! Cells `3196 ≤ n < 3198` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir094

theorem k3196_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 3).1 2).1
      858581472606772053146043777447623176044398259777359132012381193020).isSome = true := by
  decide +kernel

theorem k3196_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 3).1 2).2
      214881780869055161992638100651182514529981546355981172019127894844).isSome = true := by
  decide +kernel

theorem k3196_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 3).2 2).1
      856265666171015165876033741711394353114578906790066954767343493948).isSome = true := by
  decide +kernel

theorem k3196_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 3).2 2).2
      214289267189500972467621954434583083517593715636167941062999393084).isSome = true := by
  decide +kernel

theorem k3196_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).2 3).1 1).1
      11585569163771632738656057035976594855110767164).isSome = true := by
  decide +kernel

theorem k3196_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).2 3).1 1).2
      213632345247871657789986764846127348402100062177901528755035687484).isSome = true := by
  decide +kernel

theorem k3196_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).2 3).2
      351063556450105832543916980728956117204816978534185055362976066031252671942734813848291497480095607827064280995931932865410708284).isSome = true := by
  decide +kernel

theorem k3196_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).1 2).1
      1413251389915864748391897621843109914859205437453919043372481399154228135640127452428023772576444915985620340937844343421029183729).isSome = true := by
  decide +kernel

theorem k3196_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).1 2).2
      306622542744109968003819615716538146923499006435152011448166722111101768769384418978589951521991290031811457265).isSome = true := by
  decide +kernel

theorem k3196_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).2 2).1
      19068833218259212129187495379574013522358414084265004720258318825320537568179897863469800993738945451375141692).isSome = true := by
  decide +kernel

theorem k3196_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).2 2).2
      88010149857999609507725199214986465762251982711398818154756195982271115599485401956511147721391221112093615755710511419431568188).isSome = true := by
  decide +kernel

theorem k3197_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).1 1).1
      4747156521681558645075973458424884874072374620634349705263533911586375006982479512894263283684701717992911676).isSome = true := by
  decide +kernel

theorem k3197_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).1 1).2
      21886457515080453128468778666608254358772298281238004591122202847058543021430513406400452300867248623902557352840802675181056828).isSome = true := by
  decide +kernel

theorem k3197_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).2 1).1
      3917756047710708692970285799328948967956216488682739718770715114703633745240326132540).isSome = true := by
  decide +kernel

theorem k3197_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).2 1).2
      3917245710361057727542822885999150997888195696264901407700157073333675390286689720124).isSome = true := by
  decide +kernel

theorem k3197_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).1 1).1
      16102027005195081394285945627995585432984903820581711666339405084937582955646464183706428).isSome = true := by
  decide +kernel

theorem k3197_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).1 1).2
      1187737765667896135175143617221412810685210551961151910914114762635425158368723921737553811681315998050067260).isSome = true := by
  decide +kernel

theorem k3197_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).2 1).1
      18516042368627366465646408683204850280695865013584386446206485227728525451190730005130452718087933614082620).isSome = true := by
  decide +kernel

theorem k3197_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).2 1).2
      850122217270487011694586090303860784677826379209587349520377172796).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3196 3198 :=
  (Cover.one (box := dirCellBox) (n := 3196)
      (.split 2 (.split 3 (.split 3 (.split 2 (.leaf _ k3196_0) (.leaf _ k3196_1)) (.split 2 (.leaf _ k3196_2) (.leaf _ k3196_3))) (.split 3 (.split 1 (.leaf _ k3196_4) (.leaf _ k3196_5)) (.leaf _ k3196_6))) (.split 3 (.split 2 (.leaf _ k3196_7) (.leaf _ k3196_8)) (.split 2 (.leaf _ k3196_9) (.leaf _ k3196_10))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3197)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3197_0) (.leaf _ k3197_1)) (.split 1 (.leaf _ k3197_2) (.leaf _ k3197_3))) (.split 3 (.split 1 (.leaf _ k3197_4) (.leaf _ k3197_5)) (.split 1 (.leaf _ k3197_6) (.leaf _ k3197_7)))))

end C4.Cert.Dir094

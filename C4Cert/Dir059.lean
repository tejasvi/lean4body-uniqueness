module

public import C4Check

public section

/-! Cells `2773 ≤ n < 2774` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir059

theorem k2773_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2773) 3).1
      282657776670459105146111514042221534465060647347815797384598273495295767598752582564124772249642703856756035089661320731279630594773436075142360393036358466814345453515348308612157563).isSome = true := by
  decide +kernel

theorem k2773_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).1 2).1 1).1 3).1
      68245133470120526207240872505022107105755235882590434609182424724413142688217204038).isSome = true := by
  decide +kernel

theorem k2773_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).1 2).1 1).1 3).2
      19853368494240838805653903534855536145231805077299721092218154986964456537027639591804922594141210400326).isSome = true := by
  decide +kernel

theorem k2773_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).1 2).1 1).2 3).1
      68051653369820855862228695395017805972579098319936111662951525013770730475818656582).isSome = true := by
  decide +kernel

theorem k2773_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).1 2).1 1).2 3).2
      1458789163252411014986797529137325562271447781422992493609172641338866860588343576136538714124160460185841120510052626429426).isSome = true := by
  decide +kernel

theorem k2773_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).1 2).2
      333523214788054486627960613524325119258033835977055457832161082720252218881674947618097017234597644686647918871).isSome = true := by
  decide +kernel

theorem k2773_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).1 1).1 3).1
      6850768739717527867034309252728728045745127990552947923988247797839449553737921330190588518525043881757324817514653168275370423903175650798523846).isSome = true := by
  decide +kernel

theorem k2773_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).1 1).1 3).2
      108601189438800776774215349900492327693831029316865719843923066806565801051227367242139368607299219427133892172947985693698202762547707884390143434).isSome = true := by
  decide +kernel

theorem k2773_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).1 1).2 2).1 3).1
      16602176271041646303831062830439954060187320785302310630279929578282483209969700210).isSome = true := by
  decide +kernel

theorem k2773_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).1 1).2 2).1 3).2
      1239558141486965394534302256047056222128765179241848257316233263422914165029014710333405817125968415651068).isSome = true := by
  decide +kernel

theorem k2773_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).1 1).2 2).2
      124764414946978786999770719845277158790072379687324250071016695121536614632185722630122727200987762516178189568490727623322393999980425166653574146443659348735260147).isSome = true := by
  decide +kernel

theorem k2773_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).2 1).1
      6834246407557637874629183771281230072919971493960113778866470604370940435922634868553643949166053037336119517671982363283440618141367282104632774).isSome = true := by
  decide +kernel

theorem k2773_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2773) 3).2 3).2 2).2 1).2
      6794451815862583991191362977503625998152278787437012841118273324097741551974606006187162039706181627927363235202242556694904577756857160206484942).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2773 2774 :=
  (Cover.one (box := dirCellBox) (n := 2773)
      (.split 3 (.leaf _ k2773_0) (.split 3 (.split 2 (.split 1 (.split 3 (.leaf _ k2773_1) (.leaf _ k2773_2)) (.split 3 (.leaf _ k2773_3) (.leaf _ k2773_4))) (.leaf _ k2773_5)) (.split 2 (.split 1 (.split 3 (.leaf _ k2773_6) (.leaf _ k2773_7)) (.split 2 (.split 3 (.leaf _ k2773_8) (.leaf _ k2773_9)) (.leaf _ k2773_10))) (.split 1 (.leaf _ k2773_11) (.leaf _ k2773_12))))))

end C4.Cert.Dir059

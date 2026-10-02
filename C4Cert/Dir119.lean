module

public import C4Check

public section

/-! Cells `3593 ≤ n < 3616` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir119

theorem k3593_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3593) 2).1
      60816397648720819512406253048918385368557700193560482371768080889469841811894779463).isSome = true := by
  decide +kernel

theorem k3593_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3593) 2).2
      1563657726941475659600941336305723718301013085964214625686370736091801450792180766318271966913892422349429271176686556104168966304470973848057329).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 3594 3613 [
    1148394971993087739736273495479627817116544295926452054022365319079036831499348789911510191863082904905542,
    11162189402351850592726850834633519332725826, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c2 : allCells dirCell 3613 3614 [
    2623364969053361533683251] = true := by
  decide +kernel

theorem k3614_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3614) 3).1 3).1
      22651235173106350111234319143807513432294085580819937548836623628883147266371759514447075103920112848644608333613661791995334).isSome = true := by
  decide +kernel

theorem k3614_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3614) 3).1 3).2
      26480809071545276158879888263757648763217287008191827957033830975936237756153871092938554684915489880278610939253567958356314566669024622103201050).isSome = true := by
  decide +kernel

theorem k3614_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3614) 3).2 2).1 3).1
      4824884903118869322448554817055122085766286575836485515170999623606391367356802002404697825801937710835145).isSome = true := by
  decide +kernel

theorem k3614_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3614) 3).2 2).1 3).2
      4155474078476243703261728126718753088717673001292376976452116031833540468236537745274057).isSome = true := by
  decide +kernel

theorem k3614_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3614) 3).2 2).2 3).1
      15964506677173907756976306603606725127180780958226882329363352535639877845592600945).isSome = true := by
  decide +kernel

theorem k3614_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3614) 3).2 2).2 3).2
      259852856065381348304259615325619634397539629798212770172324143599085962496071792005833).isSome = true := by
  decide +kernel

theorem k3615_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).1 2).1
      22426332451266596711432631118113358822859425138624097490956261947727497339459107231190200102387433114560417753157819575580446513).isSome = true := by
  decide +kernel

theorem k3615_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).1 2).2
      257051773287965110257694848979354167895310182658558724878674648826257523464809000754355).isSome = true := by
  decide +kernel

theorem k3615_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).2 1).1
      4030232233287481457823724824209730512558436590091133503425342870898767876708493285170).isSome = true := by
  decide +kernel

theorem k3615_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).2 1).2
      4027563524156520673746213079086199255035874739077025029351321030833155391863199651634).isSome = true := by
  decide +kernel

theorem k3615_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).1 2).1
      18838539159494158129819818544639929868670166699055071136433022247356617918673536147484740096170663056194620).isSome = true := by
  decide +kernel

theorem k3615_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).1 2).2
      75400594431542737056576154540828847424597274276357423421931243920277763611009530474731538564757719019732028).isSome = true := by
  decide +kernel

theorem k3615_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).2 2).1
      1178474173192125943781256709571819572804712309431777823550023825283002409269662301845751001913409345935153).isSome = true := by
  decide +kernel

theorem k3615_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).2 2).2
      3994471040628731321064156746545125185977739822830257118251801853487816080474110416689).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3593 3616 :=
  (Cover.one (box := dirCellBox) (n := 3593)
      (.split 2 (.leaf _ k3593_0) (.leaf _ k3593_1))).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 3614)
      (.split 3 (.split 3 (.leaf _ k3614_0) (.leaf _ k3614_1)) (.split 2 (.split 3 (.leaf _ k3614_2) (.leaf _ k3614_3)) (.split 3 (.leaf _ k3614_4) (.leaf _ k3614_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3615)
      (.split 3 (.split 2 (.split 2 (.leaf _ k3615_0) (.leaf _ k3615_1)) (.split 1 (.leaf _ k3615_2) (.leaf _ k3615_3))) (.split 2 (.split 2 (.leaf _ k3615_4) (.leaf _ k3615_5)) (.split 2 (.leaf _ k3615_6) (.leaf _ k3615_7)))))

end C4.Cert.Dir119

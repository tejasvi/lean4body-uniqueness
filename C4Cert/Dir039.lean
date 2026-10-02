module

public import C4Check

public section

/-! Cells `2358 ≤ n < 2383` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir039

theorem k2358_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2358) 2).1
      15984229937746820471137645110621344616025715183565714446108051651897511108237160127507742).isSome = true := by
  decide +kernel

theorem k2358_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2358) 2).2 3).1
      1852832430841841192660771688999596803016893010005845194504626594160319390496220377319171838881121682660489183093031115792501581631163014789157581735237088871736845766).isSome = true := by
  decide +kernel

theorem k2358_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2358) 2).2 3).2
      21248404659620397899618035603291942033138593480452451772326837235378172451432138556635643316807179069598915516178964737212233).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 2359 2360 [
    410468600250288755428051385037028997526002375750765848102127158841833352813534459984340871376592477940319136427964783586510426303437188598614804733446] = true := by
  decide +kernel

theorem c2 : allCells dirCell 2360 2381 [
    605893986987972993369122, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k2381_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2381) 3).1
      3).isSome = true := by
  decide +kernel

theorem k2381_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2381) 3).2 3).1
      18397131432273451264883130146925882275147285562).isSome = true := by
  decide +kernel

theorem k2381_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2381) 3).2 3).2
      8251839237001572486557253033637369887101244229915765642453163010605951373378079656228034317059298704098034552355364973545149981770738216457227553600494803105544856493082).isSome = true := by
  decide +kernel

theorem k2382_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2382) 3).1 2).1 3).1
      4177977681477874856317251454745662710500426742201889386804511701329062640829894153990).isSome = true := by
  decide +kernel

theorem k2382_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2382) 3).1 2).1 3).2
      89767593449333272004380346712360149105046462180537238120976632762781565779913399388541868093377117673899909200595817323930950).isSome = true := by
  decide +kernel

theorem k2382_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2382) 3).1 2).2 3).1
      4192002109949974291043631524058614013927380087745700589156416008038154035099045304070).isSome = true := by
  decide +kernel

theorem k2382_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2382) 3).1 2).2 3).2
      22522388228998887494517971149466763997932883489936791594459327528175133133856164538098100966734092725304977314890694809267270).isSome = true := by
  decide +kernel

theorem k2382_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).1 2).1
      4692035433143409636784359245008174885482242500447269069788518311842882082626647807867418601193495797265).isSome = true := by
  decide +kernel

theorem k2382_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).1 2).2
      63712649542600581017139507820346892886273544090086188128537267816059135778823801041).isSome = true := by
  decide +kernel

theorem k2382_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).2 2).1
      297721068471672163871941702406594184990237075493100946036301268658590604596932982637384071029589032681841).isSome = true := by
  decide +kernel

theorem k2382_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).2 2).2
      4664456515544836533857841777539443949351901005513102364148697397808574490497244559324744671361343869329).isSome = true := by
  decide +kernel

theorem k2382_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).2 3).1
      22286198212241653962066301574802683720766309027553336437217976395181157966928255431559549683163445103498247146535345765161542).isSome = true := by
  decide +kernel

theorem k2382_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).2 3).2
      22098904282537399809783497721815441819821471815319878083678679678151824044164084092394345678347390413547220302180541651620166).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2358 2383 :=
  (Cover.one (box := dirCellBox) (n := 2358)
      (.split 2 (.leaf _ k2358_0) (.split 3 (.leaf _ k2358_1) (.leaf _ k2358_2)))).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 2381)
      (.split 3 (.leaf _ k2381_0) (.split 3 (.leaf _ k2381_1) (.leaf _ k2381_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2382)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2382_0) (.leaf _ k2382_1)) (.split 3 (.leaf _ k2382_2) (.leaf _ k2382_3))) (.split 2 (.split 3 (.split 2 (.leaf _ k2382_4) (.leaf _ k2382_5)) (.split 2 (.leaf _ k2382_6) (.leaf _ k2382_7))) (.split 3 (.leaf _ k2382_8) (.leaf _ k2382_9)))))

end C4.Cert.Dir039

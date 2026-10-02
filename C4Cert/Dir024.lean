module

public import C4Check

public section

/-! Cells `1994 ≤ n < 2020` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir024

theorem k1994_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1994) 2).1 3).1 1).1
      3909823128040323853903933903766252945871640318530215667347128569509616390876606617394).isSome = true := by
  decide +kernel

theorem k1994_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1994) 2).1 3).1 1).2
      3908877893696420893088434356355618201745461631461615327914213525992477372571798902578).isSome = true := by
  decide +kernel

theorem k1994_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1994) 2).1 3).2
      1393007892340405580405487578568536859610891311231990027335832050013404727000012488819484884325019452125401825096607147686977031985).isSome = true := by
  decide +kernel

theorem k1994_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1994) 2).2 3).1 1).1
      3912676015353290178467195799668529763259031056580713827082463066026466513393019967282).isSome = true := by
  decide +kernel

theorem k1994_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1994) 2).2 3).1 1).2
      3910366922074613289640461867039580897613152580745670220356921894021478745577331840819).isSome = true := by
  decide +kernel

theorem k1994_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1994) 2).2 3).2
      87096262575374520399101157286646617693556406400619717215085955382552042174419055950468736745742272391991159507539352893181611825).isSome = true := by
  decide +kernel

theorem k1995_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1995) 2).1 3).1
      15970992363881217922498688872510104032682763181953019053853458370515333108318575342036169).isSome = true := by
  decide +kernel

theorem k1995_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1995) 2).1 3).2
      249389359382979721231208944507391501525400688954936830357441509668464019577524731877169).isSome = true := by
  decide +kernel

theorem k1995_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1995) 2).2 3).1
      21751233743462127867574846921795423657094097330545930711657323559498298738447296812274803476599147263062886369960205030562061105).isSome = true := by
  decide +kernel

theorem k1995_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1995) 2).2 3).2
      3898593855481860499717196162374608978790398566150002958063993261453962433815726544689).isSome = true := by
  decide +kernel

theorem k1996_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1996) 2).1 3).1
      973966571492050427512461474921857869541317520099354767573350715738308526592498078093).isSome = true := by
  decide +kernel

theorem k1996_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1996) 2).1 3).2
      15210325971987805282097715631593966348463720545923378519357335047312727648117751153).isSome = true := by
  decide +kernel

theorem k1996_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1996) 2).2 3).1
      3896024505010437359474924609457104772862813819784271424003110293083656351588424603441).isSome = true := by
  decide +kernel

theorem k1996_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1996) 2).2 3).2
      52769157706895054380707336917567583462443205866336559037340997425).isSome = true := by
  decide +kernel

theorem k1997_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1997) 2).1
      243178228176424285190449493352868157897839077015242281777003354613618835946157649991).isSome = true := by
  decide +kernel

theorem k1997_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1997) 2).2
      1355905309955234244507797672639286623218039314785292682501394772844738751136145043228988969028252432155159138165490889751741639).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 1998 2015 [
    293835110966456375781927105080489076048135519691523750615417107667381262339711589186902567070852760075178250,
    823236737849848175648870385904423921225458965228285428471797522, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c5 : allCells dirCell 2015 2019 [
    0, 0, 0, 3] = true := by
  decide +kernel

theorem k2019_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2019) 3).1
      11831164362592315009088945177941473788853243982).isSome = true := by
  decide +kernel

theorem k2019_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2019) 3).2
      420238994716870449829944596104584500897781435482594790416722661642389535412439386605247674663908361043518813141727778663508079791802653152405437570078).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1994 2020 :=
  (Cover.one (box := dirCellBox) (n := 1994)
      (.split 2 (.split 3 (.split 1 (.leaf _ k1994_0) (.leaf _ k1994_1)) (.leaf _ k1994_2)) (.split 3 (.split 1 (.leaf _ k1994_3) (.leaf _ k1994_4)) (.leaf _ k1994_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1995)
      (.split 2 (.split 3 (.leaf _ k1995_0) (.leaf _ k1995_1)) (.split 3 (.leaf _ k1995_2) (.leaf _ k1995_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1996)
      (.split 2 (.split 3 (.leaf _ k1996_0) (.leaf _ k1996_1)) (.split 3 (.leaf _ k1996_2) (.leaf _ k1996_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1997)
      (.split 2 (.leaf _ k1997_0) (.leaf _ k1997_1))).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 2019)
      (.split 3 (.leaf _ k2019_0) (.leaf _ k2019_1)))

end C4.Cert.Dir024

module

public import C4Check

public section

/-! Cells `2355 ≤ n < 2356` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir037

theorem k2355_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).1 2).1
      6531086255055761688595073924665816898700578039834161842969556694764057436544227631989954816724065401126280436257834446055852938526985260970347753541).isSome = true := by
  decide +kernel

theorem k2355_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).1 2).2
      4689630863252845503773151292841820413541217723874311574908234668186423952544826823536370433049981752366413).isSome = true := by
  decide +kernel

theorem k2355_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).2 2).1
      101744956266707955650017833608663177115418090528421921682991735650189231854079220731193478988725794395047862894395994776811859514072979681111536881).isSome = true := by
  decide +kernel

theorem k2355_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).2 2).2
      407656440702107733960483933787754447449968150080283544480050814549487233086584622241431044951721455582840775711732428723732836546316379444776367345).isSome = true := by
  decide +kernel

theorem k2355_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).1 3).1
      298169719010157203114511566604323527007063268839002386734106292227227602009204070830415980996089015368913605).isSome = true := by
  decide +kernel

theorem k2355_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).1 3).2
      3937846735025781548674707998691183284433755116608878972607789049424618895762976823089).isSome = true := by
  decide +kernel

theorem k2355_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).2 3).1
      86054904661606906307315521336002161515708811182990476254180731378958800170958759949637791150127654029538108079575727141772721).isSome = true := by
  decide +kernel

theorem k2355_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).2 3).2
      15768536255165774465226469285152043204380765323224660281936936359896382855752202542257).isSome = true := by
  decide +kernel

theorem k2355_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).1 2).1
      73619504277195649534625333434495853507135173816430673705158763622309113661582616712526261734558630223181).isSome = true := by
  decide +kernel

theorem k2355_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).1 2).2
      18449340911469158492589409952279513577193423171145485773614940064047768542190862759917934217128272261489).isSome = true := by
  decide +kernel

theorem k2355_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).2 2).1
      4687410714066116253428004786391769690052029271773327892000113411537178407968144191744968814331591123082309).isSome = true := by
  decide +kernel

theorem k2355_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).2 2).2
      18360393004556012707989375781559535574208036668360762191801322534653088967940189431117793179464645321073).isSome = true := by
  decide +kernel

theorem k2355_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).1 2).1
      1167951804957290298844487861211275102755664056936992925858058429420849035264188942585715721784879148457393).isSome = true := by
  decide +kernel

theorem k2355_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).1 2).2
      1169796837987915294147918721107915030740144648559229732911848078016544158975373286157025600128331897068977).isSome = true := by
  decide +kernel

theorem k2355_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).2 2).1
      15787731717752371745890533532621695884957143373724025039408990706823435021197593042097).isSome = true := by
  decide +kernel

theorem k2355_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).2 2).2
      63230317603937801479474410077201713177000142683706968156905391611415874407756711424689).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2355 2356 :=
  (Cover.one (box := dirCellBox) (n := 2355)
      (.split 2 (.split 3 (.split 3 (.split 2 (.leaf _ k2355_0) (.leaf _ k2355_1)) (.split 2 (.leaf _ k2355_2) (.leaf _ k2355_3))) (.split 2 (.split 3 (.leaf _ k2355_4) (.leaf _ k2355_5)) (.split 3 (.leaf _ k2355_6) (.leaf _ k2355_7)))) (.split 3 (.split 3 (.split 2 (.leaf _ k2355_8) (.leaf _ k2355_9)) (.split 2 (.leaf _ k2355_10) (.leaf _ k2355_11))) (.split 3 (.split 2 (.leaf _ k2355_12) (.leaf _ k2355_13)) (.split 2 (.leaf _ k2355_14) (.leaf _ k2355_15))))))

end C4.Cert.Dir037

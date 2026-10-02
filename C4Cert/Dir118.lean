module

public import C4Check

public section

/-! Cells `3589 ≤ n < 3593` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir118

theorem k3589_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).1 2).1
      5339986294720041871416251496396482334609344144538050511945354895707029968187102629677236452698478907576341626321483087730492).isSome = true := by
  decide +kernel

theorem k3589_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).1 2).2
      1158448340473816700072157281501294355867269541769533697533156062979928290469569486617598464115301859412796).isSome = true := by
  decide +kernel

theorem k3589_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).2 1).1
      72237504879012690894748201509445303546088866382672728371647653697603429531759946707364306951352842966844).isSome = true := by
  decide +kernel

theorem k3589_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).2 1).2
      18056895679660741628496993705889051688272964767088708710414049459432551706310804352065315552332219353458).isSome = true := by
  decide +kernel

theorem k3589_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).1 2).1
      289801710838705889105147362831166829256246817825528581036640695622398351464188242074807216759444805767996).isSome = true := by
  decide +kernel

theorem k3589_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).1 2).2
      289987524356070470092362291668249716667297293708107258046672657693267026998752119357728650639396702769980).isSome = true := by
  decide +kernel

theorem k3589_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).2 1).1
      3919374079330742646990875029503697691397507814778593136177229254655622721614210650940).isSome = true := by
  decide +kernel

theorem k3589_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).2 1).2
      15673085405847257324123552043212697021017318833361512099042699073897351003485528118076).isSome = true := by
  decide +kernel

theorem k3590_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3590) 2).1 3).1 1).1
      3909457894479588459245636711267729691767141486454238898109007967935429471086447155004).isSome = true := by
  decide +kernel

theorem k3590_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3590) 2).1 3).1 1).2
      827648509385273699168874883843953812389323424530308537634878652).isSome = true := by
  decide +kernel

theorem k3590_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3590) 2).1 3).2
      25098032030659176646768262375978351888980867924624847939493092269732844378501161900538540155875211702116808290199329631291548917032248833048171249).isSome = true := by
  decide +kernel

theorem k3590_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3590) 2).2 3).1
      5582662108553517638515107351360760322792885360067689247508803346672062067991163401102743033971927804069709026795571445468738956529).isSome = true := by
  decide +kernel

theorem k3590_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3590) 2).2 3).2
      87135514952650792000778763168375659985436476611154896276306908954979770209949943387962913758982426083431490542008488524555711730).isSome = true := by
  decide +kernel

theorem k3591_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3591) 2).1 3).1
      5436199762292782727283080803167569877801148673050745512730564972121041422340810053140303499868398107556784797695625060612952819).isSome = true := by
  decide +kernel

theorem k3591_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3591) 2).1 3).2
      84895419619533669385592468233445604648595205450255975700673542678064521594651713648553368909553262678047681846244117451231985).isSome = true := by
  decide +kernel

theorem k3591_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3591) 2).2 3).1
      73723838900708203561030785594715459723397004350123668328038998805861681176412385610814062063108406512546044).isSome = true := by
  decide +kernel

theorem k3591_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3591) 2).2 3).2
      339642264894491705977166038710207592106367814554259242331124139608682137197443957489225366719207098497476314029463595830047987).isSome = true := by
  decide +kernel

theorem k3592_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3592) 2).1
      461823915012743833036358691197023925757509898867105203661135142206387261815086957248207917931086409449151926757138502607000600285892953973155693693571793094020474311).isSome = true := by
  decide +kernel

theorem k3592_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3592) 2).2 3).1
      339445407428062019554860512266592652782267729715093943135935546855173175673699459755755034213740518227340054519162859489686771).isSome = true := by
  decide +kernel

theorem k3592_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3592) 2).2 3).2
      3804389530587961945617402150502471592891702373662725330910682064922225032584650108).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3589 3593 :=
  (Cover.one (box := dirCellBox) (n := 3589)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3589_0) (.leaf _ k3589_1)) (.split 1 (.leaf _ k3589_2) (.leaf _ k3589_3))) (.split 3 (.split 2 (.leaf _ k3589_4) (.leaf _ k3589_5)) (.split 1 (.leaf _ k3589_6) (.leaf _ k3589_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3590)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3590_0) (.leaf _ k3590_1)) (.leaf _ k3590_2)) (.split 3 (.leaf _ k3590_3) (.leaf _ k3590_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3591)
      (.split 2 (.split 3 (.leaf _ k3591_0) (.leaf _ k3591_1)) (.split 3 (.leaf _ k3591_2) (.leaf _ k3591_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3592)
      (.split 2 (.leaf _ k3592_0) (.split 3 (.leaf _ k3592_1) (.leaf _ k3592_2))))

end C4.Cert.Dir118

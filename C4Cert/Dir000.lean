module

public import C4Check

public section

/-! Cells `0 ≤ n < 570` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir000

theorem c0 : allCells dirCell 0 265 [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1031832584442, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 61502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 61502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 61502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    61502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61502,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 241, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37735387094694377382929,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2360274012937469900353, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 2358091271250484567105, 0, 0, 0] = true := by
  decide +kernel

theorem c1 : allCells dirCell 265 400 [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2358209998715345699137,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2358322616194016610881, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 2358428524452683668545, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0] = true := by
  decide +kernel

theorem k400_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 400) 2).1
      5550314140300180088807620271206814593993983485374266517063977985771349444662489430632660663474307077753414138291593062689022358558).isSome = true := by
  decide +kernel

theorem k400_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 400) 2).2
      1934067478956108735666347314367581720031652550952468733856158297496639254008561555105031576723399584793680211805672698614179854074080333218314843970100775999139060966573083).isSome = true := by
  decide +kernel

theorem k401_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 401) 2).1
      763760423484238216111608745340577087582417716915365273449970618087346270688590436943020126).isSome = true := by
  decide +kernel

theorem k401_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 401) 2).2 2).1
      1146759520398389557576718013210998179303354242583475487528346230210659865732047042661051757657889368593607).isSome = true := by
  decide +kernel

theorem k401_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 401) 2).2 2).2
      5415396980708756890660471762756278806531374346928505766244245940420885197807811186303353783208416072481196246345498347076209975).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 402 428 [
    11410820711149936394205810135351983251103221254, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k428_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 428) 2).1 3).1
      11433698160544209285167709626947069441431883846).isSome = true := by
  decide +kernel

theorem k428_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 428) 2).1 3).2
      1387461781885269517965898503959258084507946733116227287387639733509691274230939868201819473041838917317621606499644932007897846806).isSome = true := by
  decide +kernel

theorem k428_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 428) 2).2
      1420927669567789409127538018596216755899547264638631905190039730565226573137133626631279778091656068095019067663227261665599665800391).isSome = true := by
  decide +kernel

theorem k429_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 429) 2).1 3).1 2).1
      972102384891137725335045037508819828871217518762210557417286537674684959706694981965).isSome = true := by
  decide +kernel

theorem k429_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 429) 2).1 3).1 2).2
      3887572941723635790265007161184267380824735325675199846835342015590943024884362785613).isSome = true := by
  decide +kernel

theorem k429_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 429) 2).1 3).2
      210642809046902057870238574592120411072951762377115224340043171857).isSome = true := by
  decide +kernel

theorem k429_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 429) 2).2 3).1 1).1
      243096463809253580903483848258484612955851784804884256929784348572871858067574266446).isSome = true := by
  decide +kernel

theorem k429_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 429) 2).2 3).1 1).2
      62206154493552594121656686343353523935706981323521080367446715563603866622533709552866).isSome = true := by
  decide +kernel

theorem k429_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 429) 2).2 3).2
      71691216548978671076411000260863110924908300163818162098589610774348213140813957576585770760622288437969).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 430 456 [
    3368181153709216668841944766629288579381574706867361599314650321946, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k456_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 456) 3).1
      2927594291519753942150060261203612569354154345670).isSome = true := by
  decide +kernel

theorem k456_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 456) 3).2 2).1
      1175440548317027715074239026177012692185463060518549736065434764697129112797507720993020146506718189429297229).isSome = true := by
  decide +kernel

theorem k456_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 456) 3).2 2).2
      18376764385539459625722178208493851450249348639620876192472925924290614575050285935092547454521259036164365).isSome = true := by
  decide +kernel

theorem k457_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 457) 3).1 2).1 1).1
      242847552091332701051081343081954147769165701675845139554805135720599209582148353355).isSome = true := by
  decide +kernel

theorem k457_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 457) 3).1 2).1 1).2
      62192975703832599260193038966278771431092190737702053100333491384425384711357384425863).isSome = true := by
  decide +kernel

theorem k457_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 457) 3).1 2).2 1).1
      242835726711430576795196488010055317986871487253830443856093094535397008696362367819).isSome = true := by
  decide +kernel

theorem k457_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 457) 3).1 2).2 1).2
      996299041995754302668816858533459133900039781825020577312965700736162080979261823218594).isSome = true := by
  decide +kernel

theorem k457_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 457) 3).2 2).1
      286755733383368027390597594604850795270352484573295686212401908871561857131849926225913264734413589996113).isSome = true := by
  decide +kernel

theorem k457_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 457) 3).2 2).2
      286743224242634296366690521919354716545740720772634550663666854455102161846248306731373612393638150430161).isSome = true := by
  decide +kernel

theorem c10 : allCells dirCell 458 484 [
    2852714325555166922693357869126157379367179294, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k484_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 484) 3).1
      11436571526205142697274180357290933265217147078).isSome = true := by
  decide +kernel

theorem k484_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 484) 3).2 2).1
      18369014810993808962415149732003991098353263583140556421229950998658327715689759081246746709628878933853453).isSome = true := by
  decide +kernel

theorem k484_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 484) 3).2 2).2
      4592512093104347811380152888582993933178239227832914531990209582167412364322360224930149206095644601822477).isSome = true := by
  decide +kernel

theorem k485_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 485) 3).1 2).1 1).1
      60719412360271379902371253512806185549541126134665935293225983252437341062274171211).isSome = true := by
  decide +kernel

theorem k485_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 485) 3).1 2).1 1).2
      843380740255865109160905170910841479253018895899706251457373428531).isSome = true := by
  decide +kernel

theorem k485_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 485) 3).1 2).2
      346718782718665443242727634466505098239544944207858452006681341655558317682829393536978028431541356112307612034780322905035834829).isSome = true := by
  decide +kernel

theorem k485_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 485) 3).2 2).1
      286788654150725580745574164840749799385317841088278239527752564078269134070877084041717159868483002471825).isSome = true := by
  decide +kernel

theorem k485_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 485) 3).2 2).2
      242822976464945943018442028524724380874321482128855466708760482400312733708779145553).isSome = true := by
  decide +kernel

theorem c13 : allCells dirCell 486 512 [
    2852554184159551825505450952090843851697148958, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k512_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 512) 3).1
      11444085481938529902529032502003865561192321222).isSome = true := by
  decide +kernel

theorem k512_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 512) 3).2 2).1
      15573613335920232225199771821423280982020573669350153782359912928411246329520424912133).isSome = true := by
  decide +kernel

theorem k512_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 512) 3).2 2).2
      15559190171975335459040155015318373998210913826000443791707882113490690722835286622469).isSome = true := by
  decide +kernel

theorem k513_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 513) 3).1 1).1
      1146970416025452988345668255394753964014989277542880443787691365587612177967732730458275408690276505376206).isSome = true := by
  decide +kernel

theorem k513_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 513) 3).1 1).2
      16308280926370013321065667542925190291444546480103224760621322407661321173366275136625185678).isSome = true := by
  decide +kernel

theorem k513_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 513) 3).2
      1174454080200623180026247596362316239550219258141948560247450554725111217396585255013896651517261431769402445).isSome = true := by
  decide +kernel

theorem c16 : allCells dirCell 514 540 [
    2852473986521232527559248482633934343003939870, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k540_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 540) 3).1
      44701352108252263113957723825257296687860998).isSome = true := by
  decide +kernel

theorem k540_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 540) 3).2
      86751630665479700552708478610453448763926038890964129566453651651327538293027891425702862151063589818725296916930932791975436361).isSome = true := by
  decide +kernel

theorem k541_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 541) 3).1 1).1
      60788706095193212374591027038350933094957015779302464485166463559319055515026638414).isSome = true := by
  decide +kernel

theorem k541_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 541) 3).1 1).2
      248897556223442603276624887510979604759471967584881388315886614188307550331952344831182).isSome = true := by
  decide +kernel

theorem k541_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 541) 3).2
      1147098304512069786007434221297160343494639734691114888372939319439044326709959572484409381221575835500805).isSome = true := by
  decide +kernel

theorem c19 : allCells dirCell 542 568 [
    44555813979601909753031288157852694976638214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c20 : allCells dirCell 568 569 [
    409935794144116353695421747689453400630737306056311320585803655747546706376579678450821372000721152366996698192057707811120550041117192014100157482011] = true := by
  decide +kernel

theorem k569_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 569) 3).1 2).1
      243054744169937787162543727502234650293535996519506415904818990969435180605034953073).isSome = true := by
  decide +kernel

theorem k569_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 569) 3).1 2).2
      243046700577527963226464788631142423860886422852789249014433480622620171078802897265).isSome = true := by
  decide +kernel

theorem k569_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 569) 3).2
      243036091240395662024216270867574809206454428819637827749814741271140431947783937553).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 0 570 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.one (box := dirCellBox) (n := 400)
      (.split 2 (.leaf _ k400_0) (.leaf _ k400_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 401)
      (.split 2 (.leaf _ k401_0) (.split 2 (.leaf _ k401_1) (.leaf _ k401_2)))).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 428)
      (.split 2 (.split 3 (.leaf _ k428_0) (.leaf _ k428_1)) (.leaf _ k428_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 429)
      (.split 2 (.split 3 (.split 2 (.leaf _ k429_0) (.leaf _ k429_1)) (.leaf _ k429_2)) (.split 3 (.split 1 (.leaf _ k429_3) (.leaf _ k429_4)) (.leaf _ k429_5)))).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 456)
      (.split 3 (.leaf _ k456_0) (.split 2 (.leaf _ k456_1) (.leaf _ k456_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 457)
      (.split 3 (.split 2 (.split 1 (.leaf _ k457_0) (.leaf _ k457_1)) (.split 1 (.leaf _ k457_2) (.leaf _ k457_3))) (.split 2 (.leaf _ k457_4) (.leaf _ k457_5)))).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 484)
      (.split 3 (.leaf _ k484_0) (.split 2 (.leaf _ k484_1) (.leaf _ k484_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 485)
      (.split 3 (.split 2 (.split 1 (.leaf _ k485_0) (.leaf _ k485_1)) (.leaf _ k485_2)) (.split 2 (.leaf _ k485_3) (.leaf _ k485_4)))).trans <|
  (Cover.dir c13).trans <|
  (Cover.one (box := dirCellBox) (n := 512)
      (.split 3 (.leaf _ k512_0) (.split 2 (.leaf _ k512_1) (.leaf _ k512_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 513)
      (.split 3 (.split 1 (.leaf _ k513_0) (.leaf _ k513_1)) (.leaf _ k513_2))).trans <|
  (Cover.dir c16).trans <|
  (Cover.one (box := dirCellBox) (n := 540)
      (.split 3 (.leaf _ k540_0) (.leaf _ k540_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 541)
      (.split 3 (.split 1 (.leaf _ k541_0) (.leaf _ k541_1)) (.leaf _ k541_2))).trans <|
  (Cover.dir c19).trans <|
  (Cover.dir c20).trans <|
  (Cover.one (box := dirCellBox) (n := 569)
      (.split 3 (.split 2 (.leaf _ k569_0) (.leaf _ k569_1)) (.leaf _ k569_2)))

end C4.Cert.Dir000

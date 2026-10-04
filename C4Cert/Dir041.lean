module

public import C4Check

public section

/-! Cells `2410 ≤ n < 2412` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir041

theorem k2410_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2410) 3).1 3).1
      56539201501017502875368794974472951298304700441877524180657004700316345893094962385967780843398471039474822).isSome = true := by
  decide +kernel

theorem k2410_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2410) 3).1 3).2 2).1
      4883104181723010064987686233295403352004979549024195552462595398372941459326295651614178250476314073056781).isSome = true := by
  decide +kernel

theorem k2410_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2410) 3).1 3).2 2).2
      4150238078081065087982815377877418769723966749828440776102110621955598801274370355725).isSome = true := by
  decide +kernel

theorem k2410_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).1 3).1 1).1
      184137582479949992623669340908705792744018).isSome = true := by
  decide +kernel

theorem k2410_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).1 3).1 1).2
      121621270265545092009419472124392170806739517134039151737265594637135830768068841523293361340692728511407530510217978073028574221969004240629340379088626070454629874).isSome = true := by
  decide +kernel

theorem k2410_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).1 3).2 1).1
      15903283454565934290793104146458328000241683377789385822787355472923279835007127922).isSome = true := by
  decide +kernel

theorem k2410_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).1 3).2 1).2 2).1
      18741325708658156218505548772516616262511799185614194564928934351079731306362785344604512203602802305393).isSome = true := by
  decide +kernel

theorem k2410_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).1 3).2 1).2 2).2
      3969835967805666188285373469496688305455789348667451737522689653967348363049459068).isSome = true := by
  decide +kernel

theorem k2410_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).2 3).1
      105637144191133092709156847330789233008330803272145411465654794332115949221385454725049748383269969813610747925851538523143015290976956003144242949).isSome = true := by
  decide +kernel

theorem k2410_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).2 3).2 1).1
      53968960029899704763750683606552855183255032136252268783243634).isSome = true := by
  decide +kernel

theorem k2410_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2410) 3).2 2).2 3).2 1).2
      26192674164239100975111400417142257466518388099176682461812922540670567612627665700292077490922814843797663603788342797680381423431914023194818034).isSome = true := by
  decide +kernel

theorem k2411_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).1 3).1 1).1
      5503219610973670257701555090623690796766051507887239892817021940053709956029910157568319560787793986323872201627386674238790).isSome = true := by
  decide +kernel

theorem k2411_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).1 3).1 1).2 2).1
      16141119426038847901830855973408301877130640914142353005067345495265685677409417238961).isSome = true := by
  decide +kernel

theorem k2411_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).1 3).1 1).2 2).2
      252501644710602302616071085219183835227127744137137790439511387728622910083329790321).isSome = true := by
  decide +kernel

theorem k2411_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).1 3).2 1).1
      476684457003210996201544322488344778489489143107198524293017530187693808512268459092186104201361506520673444165871843121951976511340442094810067881771727436726560206).isSome = true := by
  decide +kernel

theorem k2411_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).1 3).2 1).2 2).1
      16053872525654463610503696130598033369592997367911524442957794516745710892982309182268).isSome = true := by
  decide +kernel

theorem k2411_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).1 3).2 1).2 2).2
      251124021106633646994425118835504035903785814166838555227711616850927404773816112956).isSome = true := by
  decide +kernel

theorem k2411_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).2 3).1 1).1
      15818525871469622903430321222601019303725539692454466509067268411720521240635872626).isSome = true := by
  decide +kernel

theorem k2411_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).2 3).1 1).2
      88150707814014638304416242595558518057370217080352514136149742081578236447054998392300415484137358980394517099423448240334322).isSome = true := by
  decide +kernel

theorem k2411_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).2 3).2 1).1
      18568476489647060836844213211570289289327720935235355669796410182485020500747335211552290204810738714950).isSome = true := by
  decide +kernel

theorem k2411_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).1 2).2 3).2 1).2
      5610489174275422442212800121153165138375368077877577314606855624095173570554577029180991195276212512324718241086181177974944498).isSome = true := by
  decide +kernel

theorem k2411_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).1 3).1 2).1
      999662554437938200266771810894425064441734668987506538545131145552827439098836616625).isSome = true := by
  decide +kernel

theorem k2411_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).1 3).1 2).2
      250182968054850629561963270666502960980949942487471407731433598138653474763271691633).isSome = true := by
  decide +kernel

theorem k2411_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).1 3).2 2).1
      3990181213291505964396952753353292834287395163191904677491423896547250200010753513905).isSome = true := by
  decide +kernel

theorem k2411_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).1 3).2 2).2
      998582222839640135109289506528645997905946986106355632418054314037258524775896561073).isSome = true := by
  decide +kernel

theorem k2411_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).2 2).1 1).1
      248755828406128623647492401392801468741327766285234678330685434014392320182634249644).isSome = true := by
  decide +kernel

theorem k2411_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).2 2).1 1).2
      15914716574433197498560391230750290502309537165899329623962241232865079575518612159916).isSome = true := by
  decide +kernel

theorem k2411_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).2 2).2 1).1
      62251596579309174273114306167185930427007779150999212299191222840229194064944528812).isSome = true := by
  decide +kernel

theorem k2411_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).1 3).2 2).2 1).2
      13493793433185546286595800387462343920441167099962175341436960172).isSome = true := by
  decide +kernel

theorem k2411_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).2 3).1 1).1
      25760923460844123227466733995917820910450535862802650235589927745252249885693383182224254781295042451032310778230378766756646872068298172695696114).isSome = true := by
  decide +kernel

theorem k2411_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).2 3).1 1).2
      4842127033473841307778035478983320499813620009692955827215681586757721183209716874545031824810909668470574002).isSome = true := by
  decide +kernel

theorem k2411_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).2 3).2 2).1
      1388982364908422026645781758948632114753464948202425392842344930744723361395831737147787908990169657747413246815215405894300913).isSome = true := by
  decide +kernel

theorem k2411_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2411) 3).2 2).2 3).2 2).2
      4085064562473516793689664445962247397457741772480629346626120714846365806995604446016753).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2410 2412 :=
  (Cover.one (box := dirCellBox) (n := 2410)
      (.split 3 (.split 3 (.leaf _ k2410_0) (.split 2 (.leaf _ k2410_1) (.leaf _ k2410_2))) (.split 2 (.split 3 (.split 1 (.leaf _ k2410_3) (.leaf _ k2410_4)) (.split 1 (.leaf _ k2410_5) (.split 2 (.leaf _ k2410_6) (.leaf _ k2410_7)))) (.split 3 (.leaf _ k2410_8) (.split 1 (.leaf _ k2410_9) (.leaf _ k2410_10)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2411)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2411_0) (.split 2 (.leaf _ k2411_1) (.leaf _ k2411_2))) (.split 1 (.leaf _ k2411_3) (.split 2 (.leaf _ k2411_4) (.leaf _ k2411_5)))) (.split 3 (.split 1 (.leaf _ k2411_6) (.leaf _ k2411_7)) (.split 1 (.leaf _ k2411_8) (.leaf _ k2411_9)))) (.split 2 (.split 3 (.split 3 (.split 2 (.leaf _ k2411_10) (.leaf _ k2411_11)) (.split 2 (.leaf _ k2411_12) (.leaf _ k2411_13))) (.split 2 (.split 1 (.leaf _ k2411_14) (.leaf _ k2411_15)) (.split 1 (.leaf _ k2411_16) (.leaf _ k2411_17)))) (.split 3 (.split 1 (.leaf _ k2411_18) (.leaf _ k2411_19)) (.split 2 (.leaf _ k2411_20) (.leaf _ k2411_21))))))

end C4.Cert.Dir041

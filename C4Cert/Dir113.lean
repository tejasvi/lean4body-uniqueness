module

public import C4Check

public section

/-! Cells `3590 ≤ n < 3615` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir113

theorem k3590_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3590) 2).1 3).1 2).1
      1607500957077851353289249193415295622731112334012042640398712027606163612810871037184464299489828712833171349501512841266777198919602364274981166321).isSome = true := by
  decide +kernel

theorem k3590_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3590) 2).1 3).1 2).2
      6432241544486466379783977081487621675065980557817363601153258189141684446630680724408289656646279276270756048782044288525487384596656277096524373233).isSome = true := by
  decide +kernel

theorem k3590_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3590) 2).1 3).2 1).1
      4720922446196449994442640586879186110376251271501886500863341995918013854610688670839067666334946393263821554).isSome = true := by
  decide +kernel

theorem k3590_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3590) 2).1 3).2 1).2
      1360455025571338218915731987490857602172141910913651765924596053017214904764571618890058352442372852746331880415780242478167538).isSome = true := by
  decide +kernel

theorem k3590_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3590) 2).2 3).1 2).1 1).1
      848067757965486426247312476384699768364507365709758537334526004028).isSome = true := by
  decide +kernel

theorem k3590_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3590) 2).2 3).1 2).1 1).2
      244401245709124465311799597794467454501253287177340957745659199559676949324749176236).isSome = true := by
  decide +kernel

theorem k3590_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3590) 2).2 3).1 2).2 1).1
      53026002782810511997622046821870476872137421706606426090725832252).isSome = true := by
  decide +kernel

theorem k3590_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3590) 2).2 3).1 2).2 1).2
      53015014250349476372685497812715756053901733671151432559642639788).isSome = true := by
  decide +kernel

theorem k3590_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3590) 2).2 3).2 1).1
      1394096572770389993990529177115229140703777459204550701502728525313938864526270954363982648421897200275480320823662657161459031282).isSome = true := by
  decide +kernel

theorem k3590_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3590) 2).2 3).2 1).2
      16001135783064250221288227467660258466882836120602581372239568773550958264673442132554994).isSome = true := by
  decide +kernel

theorem k3591_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3591) 2).1 2).1 3).1
      5436535583383824200167547114556946022287482328724465188549136219720549376115833777393053907685447117847036647871407200701633265).isSome = true := by
  decide +kernel

theorem k3591_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3591) 2).1 2).1 3).2
      15225963345987376687762423065212906640506996674901645108879948171719430332102508913).isSome = true := by
  decide +kernel

theorem k3591_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3591) 2).1 2).2 3).1
      18423524473907212030787256479279363533441759201838918589872307343890576023366950902898576410695803278750961).isSome = true := by
  decide +kernel

theorem k3591_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3591) 2).1 2).2 3).2
      21225697529858902674267588602253397836008483265517020177607030583975679541765715424030467984200924361368222100564633812825329).isSome = true := by
  decide +kernel

theorem k3591_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3591) 2).2 2).1 3).1
      998810416787750508665924731437267159086036359408710731792162275965082151111880741254385).isSome = true := by
  decide +kernel

theorem k3591_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3591) 2).2 2).1 3).2
      1150855896590826740239870534779991726136061796536455831042854992837287098119332880872115171149659810782396).isSome = true := by
  decide +kernel

theorem k3591_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3591) 2).2 2).2 3).1
      294866368515881000831607642475201013191808621610945772344891863270002856499452788681641221556714916512685297).isSome = true := by
  decide +kernel

theorem k3591_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3591) 2).2 2).2 3).2
      249558310927156509441178859389893220097704191642031256946989857023545763203530127340785).isSome = true := by
  decide +kernel

theorem k3592_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3592) 2).1 3).1
      115497360343429621393649296654040022857929017423740998423757473952175292360062606443731580363977684043186056598886774919355527602530268500001625415814322279386281457).isSome = true := by
  decide +kernel

theorem k3592_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3592) 2).1 3).2
      4490125036246954769276615906698838303450153522733747580593257095573904299085346734883834475096264054257).isSome = true := by
  decide +kernel

theorem k3592_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3592) 2).2 3).1 1).1
      974340379571316030613033468771365489530794154422682850901169688301618859910475474354).isSome = true := by
  decide +kernel

theorem k3592_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3592) 2).2 3).1 1).2
      974232252827810153868251551490086567677753973445505324193173539234981192823486640828).isSome = true := by
  decide +kernel

theorem k3592_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3592) 2).2 3).2
      6259541936067105713145811423120321934731015468893891112371943020919420996154360353340578178951743671359991137624736004017805813346129541562987761).isSome = true := by
  decide +kernel

theorem k3593_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3593) 2).1
      21190814145726693114403714247135624557361829130667901449348462734352844900650949155775723210134705196948267390618587136509383).isSome = true := by
  decide +kernel

theorem k3593_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3593) 2).2 3).1
      21199579437241842925810502270409567798922638068222543561001921498440472899150667922331452984635807821782193810689900770063601).isSome = true := by
  decide +kernel

theorem k3593_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3593) 2).2 3).2
      15204683955878189724286298688823806128167164412944702805219243438225967205697090929).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 3594 3614 [
    75252858776635467207809832247991447936809245383377057102326655897054248350417819540711849304189756856310186070,
    7256031567021491501467910, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17971] = true := by
  decide +kernel

theorem k3614_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3614) 3).1 3).1
      78515586997568633112626751984039812254864673960445077326812598790812745625474925378943904734163825204379930).isSome = true := by
  decide +kernel

theorem k3614_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3614) 3).1 3).2 2).1
      6621039772166340335627748372156171037949006732713740601722176274750780181991260746142269942399678435965213282669499254648924270247185222442116550).isSome = true := by
  decide +kernel

theorem k3614_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3614) 3).1 3).2 2).2
      16048356093807088028592600872334001356914713068184377510228931992846714542782191985).isSome = true := by
  decide +kernel

theorem k3614_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3614) 3).2 2).1 3).1
      6712968921724489855751987836758890060954363533430721285169033092200147087258168141661234777685004728147722635785890745932662584446571680722745398982).isSome = true := by
  decide +kernel

theorem k3614_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3614) 3).2 2).1 3).2 2).1
      4053415220769827390068997748004696620733313727179992681907217230658964523371391063857).isSome = true := by
  decide +kernel

theorem k3614_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3614) 3).2 2).1 3).2 2).2
      16235084474900608188036879767053109932161317106165115815837407751843755591484248382641).isSome = true := by
  decide +kernel

theorem k3614_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3614) 3).2 2).2 3).1
      22190531707444956367979708527019110874927928647441462310120111383692032909251086967274572511471896573860070479525052847498697).isSome = true := by
  decide +kernel

theorem k3614_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3614) 3).2 2).2 3).2
      1227213188013573860587693784195627598951349136394584332005372990283256954388944664220840173650740258498876102).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3590 3615 :=
  (Cover.one (box := dirCellBox) (n := 3590)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3590_0) (.leaf _ k3590_1)) (.split 1 (.leaf _ k3590_2) (.leaf _ k3590_3))) (.split 3 (.split 2 (.split 1 (.leaf _ k3590_4) (.leaf _ k3590_5)) (.split 1 (.leaf _ k3590_6) (.leaf _ k3590_7))) (.split 1 (.leaf _ k3590_8) (.leaf _ k3590_9))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3591)
      (.split 2 (.split 2 (.split 3 (.leaf _ k3591_0) (.leaf _ k3591_1)) (.split 3 (.leaf _ k3591_2) (.leaf _ k3591_3))) (.split 2 (.split 3 (.leaf _ k3591_4) (.leaf _ k3591_5)) (.split 3 (.leaf _ k3591_6) (.leaf _ k3591_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3592)
      (.split 2 (.split 3 (.leaf _ k3592_0) (.leaf _ k3592_1)) (.split 3 (.split 1 (.leaf _ k3592_2) (.leaf _ k3592_3)) (.leaf _ k3592_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3593)
      (.split 2 (.leaf _ k3593_0) (.split 3 (.leaf _ k3593_1) (.leaf _ k3593_2)))).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 3614)
      (.split 3 (.split 3 (.leaf _ k3614_0) (.split 2 (.leaf _ k3614_1) (.leaf _ k3614_2))) (.split 2 (.split 3 (.leaf _ k3614_3) (.split 2 (.leaf _ k3614_4) (.leaf _ k3614_5))) (.split 3 (.leaf _ k3614_6) (.leaf _ k3614_7)))))

end C4.Cert.Dir113

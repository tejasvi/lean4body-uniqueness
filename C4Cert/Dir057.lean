module

public import C4Check

public section

/-! Cells `2747 ≤ n < 2748` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir057

theorem k2747_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).1 1).1 3).1
      1016152928684175060006514043571057562161287837979534133711266778080604284564893432650545).isSome = true := by
  decide +kernel

theorem k2747_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).1 1).1 3).2
      15859235858522648811977530746146178453697314847102404645295437008371536733602828457778).isSome = true := by
  decide +kernel

theorem k2747_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).1 1).2 3).1
      65002801872944552979222578770934989214071561974073154532849957242904216856501394502147250).isSome = true := by
  decide +kernel

theorem k2747_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).1 1).2 3).2
      253338903416357991966738413393911963639828183254438971493777343497104743417849337699505).isSome = true := by
  decide +kernel

theorem k2747_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).2 1).1 3).1
      247323164431449728161713214037956156464242185079597700259278724523051743104248273868).isSome = true := by
  decide +kernel

theorem k2747_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).2 1).1 3).2
      61745624499689436697811158149328155127468241143761938748982169169042067149281417164).isSome = true := by
  decide +kernel

theorem k2747_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).2 1).2 3).1
      13396732693066823225824346020078962983688706300358245742984920236).isSome = true := by
  decide +kernel

theorem k2747_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).2 1).2 3).2
      246837599125338640900012685777812998713566168051428861939287662164249298094473706924).isSome = true := by
  decide +kernel

theorem k2747_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).1 1).1 3).1
      65186327080359632644510281657006844270221029649344279757826197086093276354981771800555313).isSome = true := by
  decide +kernel

theorem k2747_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).1 1).1 3).2
      1016376863639995854901509499826243267214324094048677289992363259206824522710890553645873).isSome = true := by
  decide +kernel

theorem k2747_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).1 1).2 3).1
      1201685590670523153607231999531238830218255825185617621822792758251245660572397831389250055918860228409843505).isSome = true := by
  decide +kernel

theorem k2747_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).1 1).2 3).2
      1171577498237003096069886360066244692207525251056949108958043941692647857172080617022406938940800635862828).isSome = true := by
  decide +kernel

theorem k2747_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).2 1).1 3).1
      15855623738807698963028831639051835657913494075212744506511397097210671630278967282636).isSome = true := by
  decide +kernel

theorem k2747_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).2 1).1 3).2
      247378281919201588232468347881213340564123952820223923399302097419274273872395329228).isSome = true := by
  decide +kernel

theorem k2747_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).2 1).2 3).1
      63348926827724739227070318557021476237906792048027555656712301748462607071597468933681).isSome = true := by
  decide +kernel

theorem k2747_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).2 1).2 3).2
      3349877588383464719934640535298298790131874898782777095567597356).isSome = true := by
  decide +kernel

theorem k2747_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).1 3).1 1).1
      101431741853273864001620924480858457621120184126106957080856400090913494180077460893810432408118174121715584320967498803746935014741430058087243186).isSome = true := by
  decide +kernel

theorem k2747_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).1 3).1 1).2
      21471963082608804761895477816639668363589659841385031060215558687317739051889316243775802441953907276609914647359235617742258).isSome = true := by
  decide +kernel

theorem k2747_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).1 3).2 1).1
      62946933457484260422609508559299415947978537568640967386034846443002103402360142060723).isSome = true := by
  decide +kernel

theorem k2747_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).1 3).2 1).2
      21425487056900625962780953018332610484547742688053394399862617860093925097311868665251210847105708655416358451521077861375212).isSome = true := by
  decide +kernel

theorem k2747_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).2 3).1 1).1
      1408863013104428871502376365997367373642351412098308476099218046310378347628516817955937374606820897662282363684552718849538305841).isSome = true := by
  decide +kernel

theorem k2747_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).2 3).1 1).2 3).1
      13380131064690968004948526401327542755107934361313262822472907948).isSome = true := by
  decide +kernel

theorem k2747_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).2 3).1 1).2 3).2
      13363173180109111113965518834834629985823168676925182063366732972).isSome = true := by
  decide +kernel

theorem k2747_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).2 3).2 1).1
      4657703765201182861392481648884490151133330393197424944708152985950623768033131261512310237013004438101811).isSome = true := by
  decide +kernel

theorem k2747_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).2 3).2 1).2
      4647921369635246497565929355105759249029112906513768488313400354244631975539998748441535057017506315989683).isSome = true := by
  decide +kernel

theorem k2747_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).1 3).1 1).1
      5561696846610186198482744806480455446575129280343769756921816916536477450997813443363769362234697027631407553110960023422787377).isSome = true := by
  decide +kernel

theorem k2747_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).1 3).1 1).2
      1204891709265408585445869456891770601927331622168981410949033867804628384041646077868457522174197752529313585).isSome = true := by
  decide +kernel

theorem k2747_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).1 3).2 1).1
      63845363091561979527305769379411447804007615220032623854143287138993756505654486187820).isSome = true := by
  decide +kernel

theorem k2747_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).1 3).2 1).2
      18786863361678052019083707637094233754500329781757535196548267784602135768130611426644472707955199799966780).isSome = true := by
  decide +kernel

theorem k2747_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).2 3).1 1).1
      1026347694512197390970468660201787430380601618826804923202771249412193869010453291956401).isSome = true := by
  decide +kernel

theorem k2747_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).2 3).1 1).2
      16383102212118739710073236198151546054621975722661360882925437650249669417601918451678386).isSome = true := by
  decide +kernel

theorem k2747_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).2 3).2 1).1
      294457316324588579277894102074285651530698966697561559389169077773546354823581324556208695891852621872940).isSome = true := by
  decide +kernel

theorem k2747_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).2 3).2 1).2
      1020807005988741174599792123044045608232825565288522597564332412765197852360636343237692).isSome = true := by
  decide +kernel

theorem k2747_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).2 2).1 1).1 3).1
      293115121210515810917224557892108885859429430241948724921621633440418214494327212225056144544172654058444).isSome = true := by
  decide +kernel

theorem k2747_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).2 2).1 1).1 3).2
      15856890243770676220279299475156639597709577535209341084306275613897925759634610965452).isSome = true := by
  decide +kernel

theorem k2747_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).2 2).1 1).2 3).1
      15892952380080260139951617410130337421897361925897196554329451105688731436200035728444).isSome = true := by
  decide +kernel

theorem k2747_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).2 2).1 1).2 3).2
      3962000505323376756616018768444048915736696619536510269429163516827519088813642575660).isSome = true := by
  decide +kernel

theorem k2747_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).2 2).2 1).1 3).1
      15921860931791467103558168053009523652468688502355012820373746804168837485826018197292).isSome = true := by
  decide +kernel

theorem k2747_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).2 2).2 1).1 3).2
      3972332908460552228901949806585295463832589228616098788656465104717039293444484722476).isSome = true := by
  decide +kernel

theorem k2747_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).2 2).2 1).2 3).1
      15911553554230199835968910847410601471507076436569671303903985922469553211871778946108).isSome = true := by
  decide +kernel

theorem k2747_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).2 2).2 1).2 3).2
      15878650696527493650921730994373213220551916034684342840596078075277812156740178656316).isSome = true := by
  decide +kernel

theorem k2747_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).1 3).1 1).1
      1222906805591783059884984297822163335639757601329502268656157268869046330671371254272517611671165970340430838579).isSome = true := by
  decide +kernel

theorem k2747_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).1 3).1 1).2
      88084416291749833754817390412671494761331392456184678294613373790760825152055098364493976318349362824148564708908229004736691379).isSome = true := by
  decide +kernel

theorem k2747_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).1 3).2 1).1
      16177000511648158632796527674106966639974673126868639612186396233404910943282853173604147).isSome = true := by
  decide +kernel

theorem k2747_44 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).1 3).2 1).2
      1376441653862578297426798291004993289436838654294118849597601953064080631095997451971810858950496659896071740506359466785501868).isSome = true := by
  decide +kernel

theorem k2747_45 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).2 3).1 1).1
      353124387133779277323701009451827373984166208158633321030455966994008966355320605519262817856562784996383638650526558663960017715).isSome = true := by
  decide +kernel

theorem k2747_46 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).2 3).1 1).2 3).1
      15849254182501798738723697854272358061072990274609391144103902737215079061915166424124).isSome = true := by
  decide +kernel

theorem k2747_47 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).2 3).1 1).2 3).2
      53611550178635270793650252710883686247527042302911466922970561596).isSome = true := by
  decide +kernel

theorem k2747_48 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).2 3).2 1).1
      4041510887266468910561248069205928884755848637265156598076692209867334834224245101711155).isSome = true := by
  decide +kernel

theorem k2747_49 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).2 3).2 1).2
      19084685571491302857677453976432078418161708400092878647244698891666589247054655569405885164274790360958991537).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2747 2748 :=
  (Cover.one (box := dirCellBox) (n := 2747)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.split 3 (.leaf _ k2747_0) (.leaf _ k2747_1)) (.split 3 (.leaf _ k2747_2) (.leaf _ k2747_3))) (.split 1 (.split 3 (.leaf _ k2747_4) (.leaf _ k2747_5)) (.split 3 (.leaf _ k2747_6) (.leaf _ k2747_7)))) (.split 3 (.split 1 (.split 3 (.leaf _ k2747_8) (.leaf _ k2747_9)) (.split 3 (.leaf _ k2747_10) (.leaf _ k2747_11))) (.split 1 (.split 3 (.leaf _ k2747_12) (.leaf _ k2747_13)) (.split 3 (.leaf _ k2747_14) (.leaf _ k2747_15))))) (.split 2 (.split 3 (.split 1 (.leaf _ k2747_16) (.leaf _ k2747_17)) (.split 1 (.leaf _ k2747_18) (.leaf _ k2747_19))) (.split 3 (.split 1 (.leaf _ k2747_20) (.split 3 (.leaf _ k2747_21) (.leaf _ k2747_22))) (.split 1 (.leaf _ k2747_23) (.leaf _ k2747_24))))) (.split 3 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2747_25) (.leaf _ k2747_26)) (.split 1 (.leaf _ k2747_27) (.leaf _ k2747_28))) (.split 3 (.split 1 (.leaf _ k2747_29) (.leaf _ k2747_30)) (.split 1 (.leaf _ k2747_31) (.leaf _ k2747_32)))) (.split 2 (.split 1 (.split 3 (.leaf _ k2747_33) (.leaf _ k2747_34)) (.split 3 (.leaf _ k2747_35) (.leaf _ k2747_36))) (.split 1 (.split 3 (.leaf _ k2747_37) (.leaf _ k2747_38)) (.split 3 (.leaf _ k2747_39) (.leaf _ k2747_40))))) (.split 2 (.split 3 (.split 1 (.leaf _ k2747_41) (.leaf _ k2747_42)) (.split 1 (.leaf _ k2747_43) (.leaf _ k2747_44))) (.split 3 (.split 1 (.leaf _ k2747_45) (.split 3 (.leaf _ k2747_46) (.leaf _ k2747_47))) (.split 1 (.leaf _ k2747_48) (.leaf _ k2747_49)))))))

end C4.Cert.Dir057

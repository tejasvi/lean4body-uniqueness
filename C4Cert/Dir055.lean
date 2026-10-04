module

public import C4Check

public section

/-! Cells `2745 ≤ n < 2746` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir055

theorem k2745_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).1 3).1
      9536458686775425413552252535428258517282774156853501591578475573839613345771721138247445675065750521621213149753583282508560387956694793808785254289981426195351410221016424681579).isSome = true := by
  decide +kernel

theorem k2745_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).1 3).2 2).1 3).1
      24196503564440554407065719256963244993282329045920938951149279717336492625252628851475775625373745767487130876130450634475078).isSome = true := by
  decide +kernel

theorem k2745_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).1 3).2 2).1 3).2
      7005408463812822284115259652926028970772126439698938677306972575096973100809799539656364228965317757308985453701482579474875698763441915307621702).isSome = true := by
  decide +kernel

theorem k2745_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).1 3).2 2).2 3).1
      69764793485551771871998457139885613285631005119492879477010484059768215333876187718).isSome = true := by
  decide +kernel

theorem k2745_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).1 3).2 2).2 3).2
      5973153779701540143708376842167199362799070659144372156179112455919269981655117604452358969347489590123380194420071449622086).isSome = true := by
  decide +kernel

theorem k2745_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).1 2).1 3).1
      8127298532139701153478986590954099563565003227701361631559915189513681435303714097588401512592300214875682246761429759406735678491046486377149234757994753167612417478).isSome = true := by
  decide +kernel

theorem k2745_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).1 2).1 3).2 2).1
      1053894684057626707461985597445857303423335776634263461803616057952970954826219806065).isSome = true := by
  decide +kernel

theorem k2745_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).1 2).1 3).2 2).2
      264240814977829840087632569089433403451428628709243877432418343586128929363468809585).isSome = true := by
  decide +kernel

theorem k2745_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).1 2).2 3).1
      23501128930855580633871934989380807062478132433347960057274062208763563304691497837556555839961325638119264515846777190406982).isSome = true := by
  decide +kernel

theorem k2745_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).1 2).2 3).2
      23184266921530453557372023733411669277793075146140104883487798673905271915672270316966825376858910536045110793273596773994566).isSome = true := by
  decide +kernel

theorem k2745_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).2 2).1 3).1 2).1
      1042016257970294823259516288801750361346930479862240791818169215442322508166639814065).isSome = true := by
  decide +kernel

theorem k2745_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).2 2).1 3).1 2).2
      261447355475609714389328021196716443395916274430051786866931273636447403744060727665).isSome = true := by
  decide +kernel

theorem k2745_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).2 2).1 3).2 2).1
      4128807146088770589037308299050012763235488816037229868141742399359797669314420677041).isSome = true := by
  decide +kernel

theorem k2745_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).2 2).1 3).2 2).2
      1035671880944121657424735950157006028291953695973509131317837356477683870434095564209).isSome = true := by
  decide +kernel

theorem k2745_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).2 2).2 3).1 2).1
      262301737583483255556404831484053194280397691767506891277357195523390099538587619697).isSome = true := by
  decide +kernel

theorem k2745_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).2 2).2 3).1 2).2
      16429632460348540687088930126094117104608139708646702525813213653553121654442844529).isSome = true := by
  decide +kernel

theorem k2745_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).2 2).2 3).2 2).1
      259720239910627731681366028374933320784818534013535089779009681728984259595438514545).isSome = true := by
  decide +kernel

theorem k2745_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).1 3).2 3).2 2).2 3).2 2).2
      260456103387369162859733977579691809757127273520570431774983602350986881856135646577).isSome = true := by
  decide +kernel

theorem k2745_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).1 3).1
      7666426414447611914814983).isSome = true := by
  decide +kernel

theorem k2745_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).1 3).2 3).1
      82928300252318198117249694931673690749907594524676983772106099667268028093590968254404294757450005212230).isSome = true := by
  decide +kernel

theorem k2745_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).1 3).2 3).2
      7094248303920526363309753921143835508262953170506465621783138980117997959369234128184890311107656271157771553861147812836319166763463329435309514).isSome = true := by
  decide +kernel

theorem k2745_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).1 2).1 3).1
      4997825879988890161057133278830314142501250651399910876839408123550667804954998174587043657765549168114).isSome = true := by
  decide +kernel

theorem k2745_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).1 2).1 3).2
      5826488898707849538097917475499036824281587885386916445187746862783395331496703137881377072104129574749656605288500169868102).isSome = true := by
  decide +kernel

theorem k2745_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).1 2).2
      6903104270718205121929334079644125081693274037685437203510426390691255824774604718835956709433428754546907777125449085979522979649730280489076551).isSome = true := by
  decide +kernel

theorem k2745_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).2 2).1 3).1
      23027577643175990484899873755835214711951032386489501115506981217832087887425665825379347013134217643796812356412871880774214).isSome = true := by
  decide +kernel

theorem k2745_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).2 2).1 3).2
      1459969522360067336011547138026397178812040745912750501846551514804511000393461156778400395826645171854601655610278578868090354).isSome = true := by
  decide +kernel

theorem k2745_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).2 2).2 3).1
      4887677452782111745875764072950173122370789408694933133989353660319766883190578740975695272629060769266).isSome = true := by
  decide +kernel

theorem k2745_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).1 2).2 3).2 3).2 2).2 3).2
      77475642024095358623672022172007602038141837080986048768732845590550965630584981039384289037187803705417).isSome = true := by
  decide +kernel

theorem k2745_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).1 3).1 2).1
      25262720325431104313163333461593971206413192538263859057628445925904241376073339436998663261487435460458755752957601807603142).isSome = true := by
  decide +kernel

theorem k2745_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).1 3).1 2).2
      18267467164670822913897157028183903139748223777812864792902548273054777580301608306).isSome = true := by
  decide +kernel

theorem k2745_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).1 3).2 2).1 2).1
      5205546132420395492689222996418911722901189454350510032864855481078602946236665772030581255061684451697).isSome = true := by
  decide +kernel

theorem k2745_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).1 3).2 2).1 2).2
      17697018249708872934232304773234154658497572028737587115519380157034783524780972401).isSome = true := by
  decide +kernel

theorem k2745_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).1 3).2 2).2
      70711463754075524864168231877641501904603825649657400137808964562216040483781051206).isSome = true := by
  decide +kernel

theorem k2745_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).2 2).1 3).1 2).1
      24033739590082252563492030221189746115743082079500511369651643023043035410955701008778310518336496616277533914599107696485873).isSome = true := by
  decide +kernel

theorem k2745_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).2 2).1 3).1 2).2
      17202156939192428862319347139643986455353855760521652862210145123742882517569339761).isSome = true := by
  decide +kernel

theorem k2745_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).2 2).1 3).2 2).1
      1275114856621972152981975228074716230385533890379707411950368774217547848812390422106169460782638604248561).isSome = true := by
  decide +kernel

theorem k2745_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).2 2).1 3).2 2).2
      1278879397605199714816978298537849245895959162081430288803391412725550102942042647230288574811266008573425).isSome = true := by
  decide +kernel

theorem k2745_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).2 2).2 3).1
      1789463538868363022250377862770361220392869498481752164108662504572701827208736158340876717950566114962176065609997053630622756202785115136161266).isSome = true := by
  decide +kernel

theorem k2745_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).1 3).2 2).2 3).2
      517095993414349486949331144146575535323716045418076956435985175249533814086621417660605858762184861505798729185664339825250622754331359781502829123236219985005348294).isSome = true := by
  decide +kernel

theorem k2745_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).1 3).1 2).1
      20136733169420325014283463619120207819838022873376548414687298029870082685110383700377245697557236684788465).isSome = true := by
  decide +kernel

theorem k2745_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).1 3).1 2).2
      1263211445689537139460184716504012273980778819033587505173203453479368032345517420007913529774518054184433).isSome = true := by
  decide +kernel

theorem k2745_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).1 3).2 2).1
      19866777985742454554155001938403575905084528447480391567941108797580398340690488683935027982088492938270641).isSome = true := by
  decide +kernel

theorem k2745_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).1 3).2 2).2
      270269998160545163146861754490014408163377107919730792637072146016310313926134231306993).isSome = true := by
  decide +kernel

theorem k2745_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).2 3).1 2).1
      17142410204790912784178236302561739483024494612784281244015517274786187909209414792444).isSome = true := by
  decide +kernel

theorem k2745_44 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).2 3).1 2).2
      16762752979110339539947457527879798823218720494719756713452564824443438457706526065).isSome = true := by
  decide +kernel

theorem k2745_45 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).2 3).2 2).1
      67796203506271181881329942461300710486944306595731141008971714339267901856697201824497).isSome = true := by
  decide +kernel

theorem k2745_46 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).1 2).2 3).2 2).2
      19610294479416960573587472716158831849490071657756668003812761985811910983372510312071645574415410683324).isSome = true := by
  decide +kernel

theorem k2745_47 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).1 3).1 2).1
      266249117397618664150601137999704153485607547880081226198995598615173573037090275354289).isSome = true := by
  decide +kernel

theorem k2745_48 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).1 3).1 2).2
      16701313079207601038272958119120352130833000668680239584713270865644215461102802868657).isSome = true := by
  decide +kernel

theorem k2745_49 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).1 3).2 2).1
      1055121417769379389251203991906954296420266477372549910427702840817616028803431286023857).isSome = true := by
  decide +kernel

theorem k2745_50 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).1 3).2 2).2
      66167248760523568231785835990516492705563941356957024222787451853184672533063673321905).isSome = true := by
  decide +kernel

theorem k2745_51 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).2 3).1 2).1
      4189369046669770399051882444719353042091790086569897846519157603754881646490974509489).isSome = true := by
  decide +kernel

theorem k2745_52 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).2 3).1 2).2
      14230117303403105946521100982561927599361474178047586053125725372).isSome = true := by
  decide +kernel

theorem k2745_53 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).2 3).2 2).1
      4149017121034270373511800114245151179604045659799372132396860066676447169214444706225).isSome = true := by
  decide +kernel

theorem k2745_54 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).1 3).2 3).2 2).2 3).2 2).2
      14104019138301128985120320568213581643172498895121336742866213692).isSome = true := by
  decide +kernel

theorem k2745_55 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).1 3).1
      1805408332866380599258646303946133336321659255529664716883681492353683547).isSome = true := by
  decide +kernel

theorem k2745_56 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).1 3).2 3).1
      24386403227655954755153286217031308681553087532324460345978185231705477646871276183361585699634128049936512162042912676820426).isSome = true := by
  decide +kernel

theorem k2745_57 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).1 3).2 3).2 2).1
      1490192373186647948291419350017622296437776547888938124055669033822431819658278870863745838700722929494711293391439660152306).isSome = true := by
  decide +kernel

theorem k2745_58 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).1 3).2 3).2 2).2
      17191673309761816138567537606280345805817895752112649876294214727956629474378513777).isSome = true := by
  decide +kernel

theorem k2745_59 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).1 2).1 3).1
      128284663343757743589331558758692707868574029280993735299795415599175123317819606459398080036431891772273672460563683006116210153843543105112694107405841338863810034).isSome = true := by
  decide +kernel

theorem k2745_60 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).1 2).1 3).2
      1488498808471154529570268480315570188865322982690371554508848787393108880801210964997011453104789574570417955278044984079668978).isSome = true := by
  decide +kernel

theorem k2745_61 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).1 2).2 3).1
      16863752593653317076916714906905967540892962628620322404682497286609914412008601969).isSome = true := by
  decide +kernel

theorem k2745_62 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).1 2).2 3).2
      19697060550704607140908022125571265657838269226587596779489219061544156821923291167756299641021114770930).isSome = true := by
  decide +kernel

theorem k2745_63 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).2 2).1 3).1
      5096984973934904334498789905185540717085354335041867655124978402420599486281619418190575083777508110622094066).isSome = true := by
  decide +kernel

theorem k2745_64 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).2 2).1 3).2
      373112682883844341808784296230041972940502480120776198507920973815926536129575395081615785406679769442191165123825602712937526002).isSome = true := by
  decide +kernel

theorem k2745_65 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).2 2).2 3).1
      23029797059674988227234597191806651235162944708646587680623075131363030223254391671491325649333562984167673950972033174169073).isSome = true := by
  decide +kernel

theorem k2745_66 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2745) 1).2 2).2 3).2 3).2 2).2 3).2
      1074727619639499383618605278834250321214442972061970786109641643766096118406132885197554).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2745 2746 :=
  (Cover.one (box := dirCellBox) (n := 2745)
      (.split 1 (.split 2 (.split 3 (.split 3 (.leaf _ k2745_0) (.split 2 (.split 3 (.leaf _ k2745_1) (.leaf _ k2745_2)) (.split 3 (.leaf _ k2745_3) (.leaf _ k2745_4)))) (.split 3 (.split 2 (.split 3 (.leaf _ k2745_5) (.split 2 (.leaf _ k2745_6) (.leaf _ k2745_7))) (.split 3 (.leaf _ k2745_8) (.leaf _ k2745_9))) (.split 2 (.split 3 (.split 2 (.leaf _ k2745_10) (.leaf _ k2745_11)) (.split 2 (.leaf _ k2745_12) (.leaf _ k2745_13))) (.split 3 (.split 2 (.leaf _ k2745_14) (.leaf _ k2745_15)) (.split 2 (.leaf _ k2745_16) (.leaf _ k2745_17)))))) (.split 3 (.split 3 (.leaf _ k2745_18) (.split 3 (.leaf _ k2745_19) (.leaf _ k2745_20))) (.split 3 (.split 2 (.split 3 (.leaf _ k2745_21) (.leaf _ k2745_22)) (.leaf _ k2745_23)) (.split 2 (.split 3 (.leaf _ k2745_24) (.leaf _ k2745_25)) (.split 3 (.leaf _ k2745_26) (.leaf _ k2745_27)))))) (.split 2 (.split 3 (.split 3 (.split 3 (.split 2 (.leaf _ k2745_28) (.leaf _ k2745_29)) (.split 2 (.split 2 (.leaf _ k2745_30) (.leaf _ k2745_31)) (.leaf _ k2745_32))) (.split 2 (.split 3 (.split 2 (.leaf _ k2745_33) (.leaf _ k2745_34)) (.split 2 (.leaf _ k2745_35) (.leaf _ k2745_36))) (.split 3 (.leaf _ k2745_37) (.leaf _ k2745_38)))) (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k2745_39) (.leaf _ k2745_40)) (.split 2 (.leaf _ k2745_41) (.leaf _ k2745_42))) (.split 3 (.split 2 (.leaf _ k2745_43) (.leaf _ k2745_44)) (.split 2 (.leaf _ k2745_45) (.leaf _ k2745_46)))) (.split 2 (.split 3 (.split 2 (.leaf _ k2745_47) (.leaf _ k2745_48)) (.split 2 (.leaf _ k2745_49) (.leaf _ k2745_50))) (.split 3 (.split 2 (.leaf _ k2745_51) (.leaf _ k2745_52)) (.split 2 (.leaf _ k2745_53) (.leaf _ k2745_54)))))) (.split 3 (.split 3 (.leaf _ k2745_55) (.split 3 (.leaf _ k2745_56) (.split 2 (.leaf _ k2745_57) (.leaf _ k2745_58)))) (.split 3 (.split 2 (.split 3 (.leaf _ k2745_59) (.leaf _ k2745_60)) (.split 3 (.leaf _ k2745_61) (.leaf _ k2745_62))) (.split 2 (.split 3 (.leaf _ k2745_63) (.leaf _ k2745_64)) (.split 3 (.leaf _ k2745_65) (.leaf _ k2745_66))))))))

end C4.Cert.Dir055

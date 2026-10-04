module

public import C4Check

public section

/-! Cells `2746 ≤ n < 2747` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir056

theorem k2746_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).1 3).1 1).1 2).1
      65540440764872594221033824228031947734551773571092238932072299251302640867857107655089).isSome = true := by
  decide +kernel

theorem k2746_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).1 3).1 1).1 2).2
      4108917484644044494025194281011730362005660345960686422073964808858503115539352295857).isSome = true := by
  decide +kernel

theorem k2746_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).1 3).1 1).2 2).1
      77227055824761860716841742667624684959888307455179740934591323451766426068280162191863189940895813188024753).isSome = true := by
  decide +kernel

theorem k2746_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).1 3).1 1).2 2).2
      65636412519697386471615360190596142921422736369088780454686910694002102623565604297137).isSome = true := by
  decide +kernel

theorem k2746_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).1 3).2 2).1 1).1
      1041073741967825900997375106126802556502505056522809733038390912658448477987850319584689).isSome = true := by
  decide +kernel

theorem k2746_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).1 3).2 2).1 1).2
      1039906809672021195929584463003011458684050597021371341588753899442099115430387116767409).isSome = true := by
  decide +kernel

theorem k2746_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).1 3).2 2).2 1).1
      4080637392712020420030628408941186502534258617674906423322966420997368183903848962481).isSome = true := by
  decide +kernel

theorem k2746_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).1 3).2 2).2 1).2
      65216062311420676399187630558724115756999850718511818594923539334779349690954506827436).isSome = true := by
  decide +kernel

theorem k2746_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).1 3).1 2).1
      1030205139202852681572146339773599474383582597028809314408987230544443401058294212017).isSome = true := by
  decide +kernel

theorem k2746_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).1 3).1 2).2
      258242144279822916250940211878797941893485326957920401194111689535838821943375652209).isSome = true := by
  decide +kernel

theorem k2746_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).1 3).2 2).1
      221862458319308787514400616583379125206281185373499669092391965420).isSome = true := by
  decide +kernel

theorem k2746_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).1 3).2 2).2
      13901552092245720883883549112865798690730783469746085187112375020).isSome = true := by
  decide +kernel

theorem k2746_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).2 3).1 2).1
      4116678181662754237760510900350604455678950924132634705921750792142799131680936975596).isSome = true := by
  decide +kernel

theorem k2746_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).2 3).1 2).2
      13986054380655013608405539775536551285805999291314307856449821932).isSome = true := by
  decide +kernel

theorem k2746_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).2 3).2 2).1
      4086975019428737029287222208089155144806021069769374119626588903167263044521178949292).isSome = true := by
  decide +kernel

theorem k2746_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).2 3).2 2).2
      55539812840291143553114249904559582952299906695884660775198365612).isSome = true := by
  decide +kernel

theorem k2746_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).1 3).1 1).1 2).1
      258831561961291423239110573960546910716589775872853766483404829985141655541763679542705).isSome = true := by
  decide +kernel

theorem k2746_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).1 3).1 1).1 2).2
      14066458173702881622874613544402418782769999108181307516901304162737).isSome = true := by
  decide +kernel

theorem k2746_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).1 3).1 1).2 2).1
      258700752332856066140596514955878359083805142868770222697064753806423258632523162713260).isSome = true := by
  decide +kernel

theorem k2746_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).1 3).1 1).2 2).2
      64832257591818483837612424380574812227440344978807825991741597237506328572960320126124).isSome = true := by
  decide +kernel

theorem k2746_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).1 3).2 1).1 2).1
      16102292724480102403479127866390778640167933823107446897584369659056664594979259309233).isSome = true := by
  decide +kernel

theorem k2746_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).1 3).2 1).1 2).2
      758796161944380964973471387921638773125796750001).isSome = true := by
  decide +kernel

theorem k2746_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).1 3).2 1).2 2).1
      64363914051969804650575801057948374054332058639174008800859264707685826789221556600620).isSome = true := by
  decide +kernel

theorem k2746_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).1 3).2 1).2 2).2
      16130667858227101340501559149376906335252908143691044362721890198763893728328762097452).isSome = true := by
  decide +kernel

theorem k2746_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).2 3).1 1).1
      90925944877472736434199432607817839717325585867709872692169204904533386907224719579214348536365497717228433545092282701412955826).isSome = true := by
  decide +kernel

theorem k2746_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).2 3).1 1).2 2).1
      763470835879663368802120114755269632124463637169).isSome = true := by
  decide +kernel

theorem k2746_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).2 3).1 1).2 2).2
      3449329229810919013597906184167417876918562545438958865498892716).isSome = true := by
  decide +kernel

theorem k2746_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).2 3).2 2).1 1).1
      54840496971765810189166043216939656815786349777039213307743534508).isSome = true := by
  decide +kernel

theorem k2746_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).2 3).2 2).1 1).2
      54764843919505210427911673942756971758039163905054879949949106348).isSome = true := by
  decide +kernel

theorem k2746_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).2 3).2 2).2 1).1
      13739391714073446566058799322583770672182840476860329927526415788).isSome = true := by
  decide +kernel

theorem k2746_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).2 3).2 2).2 1).2
      47577279059684595953945782875723549412184250545).isSome = true := by
  decide +kernel

theorem k2746_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).1 1).1 3).1
      23160640211889708096457666003534610593493707597356184895420551570331053727071151337556874671605914588473646922568678119992816370).isSome = true := by
  decide +kernel

theorem k2746_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).1 1).1 3).2
      1245726854071111601323919957936512409087242855381737034290722191027735944266868273553883743358317069764283314).isSome = true := by
  decide +kernel

theorem k2746_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).1 1).2 3).1
      92491771979834164535932356584085810628173750965993461770887225202377942040684369083736904346567726879330167351077782747545754866).isSome = true := by
  decide +kernel

theorem k2746_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).1 1).2 3).2
      1077994103665752888435908703234648751482510057318684870079112853050530042141253524292971762).isSome = true := by
  decide +kernel

theorem k2746_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).2 1).1 3).1
      22699840207331138139658666442490812123780902021751535730845826791993497817674446975692953842397073837442478983556564845028850).isSome = true := by
  decide +kernel

theorem k2746_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).2 1).1 3).2
      4885631206026121802609445337446270586953591277556387203031435256903735717413654728971192277535852762862322).isSome = true := by
  decide +kernel

theorem k2746_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).2 1).2 2).1
      16892691628841052496571430659347297064339558168984167321255257351711897048345431228435379).isSome = true := by
  decide +kernel

theorem k2746_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).2 1).2 2).2
      1057685209329635064351244452291498714854160417938506974923427350239525762126534336144627).isSome = true := by
  decide +kernel

theorem k2746_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).1 2).1 3).1
      19337582763280450894116815711084917169800482023607459992489032352893987906236704806014723227291597471606450).isSome = true := by
  decide +kernel

theorem k2746_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).1 2).1 3).2
      76906699532481015442670828429026994117682069876779790719907779484745289126787797145045112632360110598252210).isSome = true := by
  decide +kernel

theorem k2746_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).1 2).2 3).1
      263021072829583260205612463294380206570755987490631992999304071242316283116334344725746).isSome = true := by
  decide +kernel

theorem k2746_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).1 2).2 3).2
      16344057965985274012830857987543733191312166259810789794452500993487411538530031920818).isSome = true := by
  decide +kernel

theorem k2746_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).2 2).1 3).1
      268008573812790494193129734485404809197785339423156892788404536552198122263567434074678962).isSome = true := by
  decide +kernel

theorem k2746_44 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).2 2).1 3).2
      76818508557985041349827883229295173487898741996238369072313364008999283735672589610161054444091274793707186).isSome = true := by
  decide +kernel

theorem k2746_45 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).2 2).2 2).1
      4171882201007667688546323705680187001058661666776946981982668408948955662843088364542643).isSome = true := by
  decide +kernel

theorem k2746_46 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).2 2).2 2).2
      261188369252604742614228602161544401463776576004617284338103878237511379614550382241459).isSome = true := by
  decide +kernel

theorem k2746_47 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).1 1).1 3).1
      358549334548519163093581500213122109547379096653669736749236354246218791084915581223132580686983170380601244445500672198085016754).isSome = true := by
  decide +kernel

theorem k2746_48 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).1 1).1 3).2
      89320685608871548241289896986110581352098387846674456346063246513435287981357856835865815865721850337671064647217126862925429938).isSome = true := by
  decide +kernel

theorem k2746_49 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).1 1).2 3).1 2).1
      13893685499276638067824827149741278971716460922216478224801571233329).isSome = true := by
  decide +kernel

theorem k2746_50 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).1 1).2 3).1 2).2
      4015322427702273542654475221703199390433947138626865901209648160098578484932898156332).isSome = true := by
  decide +kernel

theorem k2746_51 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).1 1).2 3).2
      89238446679664207560137834087277423980478977562424671488027495260445348915030367457653626837804591715453758721005405182627511474).isSome = true := by
  decide +kernel

theorem k2746_52 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).2 1).1 3).1
      22239065611892017511435145469338762181511371063850269944578733035498812381028784122952760102650978213793513131196173019659001649).isSome = true := by
  decide +kernel

theorem k2746_53 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).2 1).1 3).2
      16293236686651248782514175997199087727618156685293178835631890053747672082764394721070897).isSome = true := by
  decide +kernel

theorem k2746_54 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).2 1).2 3).1
      19268529270483235144963656260476905146241104375922622992713668848187674423325925535711023578824848600561449777).isSome = true := by
  decide +kernel

theorem k2746_55 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).2 1).2 3).2
      76910860757799048567592569913946171677155155016894242425606774570258590617944167972359372035826706954557218609).isSome = true := by
  decide +kernel

theorem k2746_56 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).1 3).1 2).1 1).1
      189279484152644829379698167898667441084785514673).isSome = true := by
  decide +kernel

theorem k2746_57 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).1 3).1 2).1 1).2
      16095907130946689482308984854849620922751117716527226690617329319397739131885978484524).isSome = true := by
  decide +kernel

theorem k2746_58 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).1 3).1 2).2 1).1
      13675587518861463197893614433225189345664571833355471892855225772).isSome = true := by
  decide +kernel

theorem k2746_59 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).1 3).1 2).2 1).2
      54633763029104157753143557177224053139726521058385619741577705644).isSome = true := by
  decide +kernel

theorem k2746_60 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).1 3).2 2).1
      77528934872771301916078918991508173609039314513637093084868010082020143252355888842373930102560884086764305585).isSome = true := by
  decide +kernel

theorem k2746_61 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).1 3).2 2).2
      16857769170669858238792155074302227904983754132583392065946641847383202780595912343884489413).isSome = true := by
  decide +kernel

theorem k2746_62 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).2 1).1 3).1
      89323889333912255137044835494081931298757574908247129083669929740329268704015056952553072821924645755699157310916454600647736498).isSome = true := by
  decide +kernel

theorem k2746_63 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).2 1).1 3).2
      5567083366888209564828522268695274245218432434733407211470367185148070579440623743236321964979036795663354375262929593678847793).isSome = true := by
  decide +kernel

theorem k2746_64 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).2 1).2 3).1
      19353335131703758487205264105385584264482491612962908599989205009232460480399666628327467867474178395929672882).isSome = true := by
  decide +kernel

theorem k2746_65 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).2 1).2 3).2
      4818756119447467282868175546718304822642132991148245512695751959107659686739694882561350177001220453367905073).isSome = true := by
  decide +kernel

theorem k2746_66 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).1 3).1 1).1
      5646553829258983249964988294574241214889402305991389459467132378218603586190686709472421959482464826199788700012950564988380850).isSome = true := by
  decide +kernel

theorem k2746_67 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).1 3).1 1).2
      305785562814133839406486889816160065082434516672116631111584100355292686744476101786839430933675916756640434).isSome = true := by
  decide +kernel

theorem k2746_68 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).1 3).2 2).1
      4862396412769773643438678868021205453430151350697288868005455031853264932835203892443960500241256352263536049).isSome = true := by
  decide +kernel

theorem k2746_69 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).1 3).2 2).2
      76098783419948932516153561951180268016670186152652836536570599082767986589471459900777578022586761764501937).isSome = true := by
  decide +kernel

theorem k2746_70 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).2 1).1 3).1
      4065152704798568915975651115635006219474746995961144309438738020315888959323838110130).isSome = true := by
  decide +kernel

theorem k2746_71 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).2 1).1 3).2
      1194453325062678192695893502775911298621239044955101999707113506145891204532693587718550726534567227914674).isSome = true := by
  decide +kernel

theorem k2746_72 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).2 1).2 2).1
      16527404336864969337421529704572552128256517262474636027202363262359847289663953124042419).isSome = true := by
  decide +kernel

theorem k2746_73 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).2 1).2 2).2
      1034865485655171709454051669197586633918930153790807940581291750446064754156336960874163).isSome = true := by
  decide +kernel

theorem k2746_74 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).1 3).1 1).1
      4208813466470330801269509288730936452821024633890796734572270162876147036606675149713175217).isSome = true := by
  decide +kernel

theorem k2746_75 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).1 3).1 1).2
      263063996643890983512521668359619897671023847137505797368164625308156141311383116880379058).isSome = true := by
  decide +kernel

theorem k2746_76 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).1 3).2 1).1
      16782384162328266160863699833652012883986529200096916653982635016227220605798735194909120713).isSome = true := by
  decide +kernel

theorem k2746_77 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).1 3).2 1).2
      1048952822928310825445331558419019542776781827852028216478576296068760112745089581521140914).isSome = true := by
  decide +kernel

theorem k2746_78 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).2 3).1 1).1
      351154295300412636170744510357504987982316550376683370192473977567888870164952834959976717141207991330580469503499240643066290).isSome = true := by
  decide +kernel

theorem k2746_79 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).2 3).1 1).2
      16488394104280461948349378605790308447005709969590907975303888764141457421416691478684338).isSome = true := by
  decide +kernel

theorem k2746_80 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).2 3).2 1).1
      4108057782970713111265026185618692845047291785960841091250414581545121259911630795694769).isSome = true := by
  decide +kernel

theorem k2746_81 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).2 3).2 1).2
      4104562992450568982242025877582889851623549391757183209911693071015708676860268238698673).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2746 2747 :=
  (Cover.one (box := dirCellBox) (n := 2746)
      (.split 3 (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k2746_0) (.leaf _ k2746_1)) (.split 2 (.leaf _ k2746_2) (.leaf _ k2746_3))) (.split 2 (.split 1 (.leaf _ k2746_4) (.leaf _ k2746_5)) (.split 1 (.leaf _ k2746_6) (.leaf _ k2746_7)))) (.split 1 (.split 3 (.split 2 (.leaf _ k2746_8) (.leaf _ k2746_9)) (.split 2 (.leaf _ k2746_10) (.leaf _ k2746_11))) (.split 3 (.split 2 (.leaf _ k2746_12) (.leaf _ k2746_13)) (.split 2 (.leaf _ k2746_14) (.leaf _ k2746_15))))) (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k2746_16) (.leaf _ k2746_17)) (.split 2 (.leaf _ k2746_18) (.leaf _ k2746_19))) (.split 1 (.split 2 (.leaf _ k2746_20) (.leaf _ k2746_21)) (.split 2 (.leaf _ k2746_22) (.leaf _ k2746_23)))) (.split 3 (.split 1 (.leaf _ k2746_24) (.split 2 (.leaf _ k2746_25) (.leaf _ k2746_26))) (.split 2 (.split 1 (.leaf _ k2746_27) (.leaf _ k2746_28)) (.split 1 (.leaf _ k2746_29) (.leaf _ k2746_30)))))) (.split 3 (.split 2 (.split 1 (.split 3 (.leaf _ k2746_31) (.leaf _ k2746_32)) (.split 3 (.leaf _ k2746_33) (.leaf _ k2746_34))) (.split 1 (.split 3 (.leaf _ k2746_35) (.leaf _ k2746_36)) (.split 2 (.leaf _ k2746_37) (.leaf _ k2746_38)))) (.split 1 (.split 2 (.split 3 (.leaf _ k2746_39) (.leaf _ k2746_40)) (.split 3 (.leaf _ k2746_41) (.leaf _ k2746_42))) (.split 2 (.split 3 (.leaf _ k2746_43) (.leaf _ k2746_44)) (.split 2 (.leaf _ k2746_45) (.leaf _ k2746_46)))))) (.split 2 (.split 2 (.split 3 (.split 1 (.split 3 (.leaf _ k2746_47) (.leaf _ k2746_48)) (.split 3 (.split 2 (.leaf _ k2746_49) (.leaf _ k2746_50)) (.leaf _ k2746_51))) (.split 1 (.split 3 (.leaf _ k2746_52) (.leaf _ k2746_53)) (.split 3 (.leaf _ k2746_54) (.leaf _ k2746_55)))) (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k2746_56) (.leaf _ k2746_57)) (.split 1 (.leaf _ k2746_58) (.leaf _ k2746_59))) (.split 2 (.leaf _ k2746_60) (.leaf _ k2746_61))) (.split 1 (.split 3 (.leaf _ k2746_62) (.leaf _ k2746_63)) (.split 3 (.leaf _ k2746_64) (.leaf _ k2746_65))))) (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2746_66) (.leaf _ k2746_67)) (.split 2 (.leaf _ k2746_68) (.leaf _ k2746_69))) (.split 1 (.split 3 (.leaf _ k2746_70) (.leaf _ k2746_71)) (.split 2 (.leaf _ k2746_72) (.leaf _ k2746_73)))) (.split 2 (.split 3 (.split 1 (.leaf _ k2746_74) (.leaf _ k2746_75)) (.split 1 (.leaf _ k2746_76) (.leaf _ k2746_77))) (.split 3 (.split 1 (.leaf _ k2746_78) (.leaf _ k2746_79)) (.split 1 (.leaf _ k2746_80) (.leaf _ k2746_81))))))))

end C4.Cert.Dir056

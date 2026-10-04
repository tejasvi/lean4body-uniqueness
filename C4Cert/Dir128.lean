module

public import C4Check

public section

/-! Cells `4006 ≤ n < 4009` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir128

theorem k4006_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).1 2).1 3).1
      76577321671035196578869037416135413947776456237268422202325279151635490348816223099244788525602064134726).isSome = true := by
  decide +kernel

theorem k4006_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).1 2).1 3).2
      310683370426844687390841645241341400893450925384140207305507296807717659865901984101216569042488473501525190).isSome = true := by
  decide +kernel

theorem k4006_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4006) 3).1 2).2
      105689195519421634567517131987008015096296439339749689799882485596412663956862388113450880112306695122829527120481160141984331337188887349255020871).isSome = true := by
  decide +kernel

theorem k4006_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).2 2).1 3).1
      4277441971106028160240006777967566408734966808085892546747110947399946384094130214066639750).isSome = true := by
  decide +kernel

theorem k4006_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).2 2).1 3).2
      312917670385862241195297680986763853087658027071246424510461610899404360031037615310957254776540601982484176070).isSome = true := by
  decide +kernel

theorem k4006_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).2 2).2 3).1
      1042463974224498900503671971561309519364805393922500195688008569205378662019102538646726).isSome = true := by
  decide +kernel

theorem k4006_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4006) 3).2 2).2 3).2
      1060697526049922697616947868038471075393228442904105558840389217563945311638356477271034758).isSome = true := by
  decide +kernel

theorem k4007_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).1 2).1 3).1
      257465196784456871317479148280128490054999900649587092352719698331037682744339517634181).isSome = true := by
  decide +kernel

theorem k4007_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).1 2).1 3).2
      256198133973945187698251257509942004211348800873151213280863443864795224259989640078985).isSome = true := by
  decide +kernel

theorem k4007_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).1 2).2 3).1
      54498747769422970670555473955735186084814743424487796794458003249).isSome = true := by
  decide +kernel

theorem k4007_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).1 2).2 3).2
      64090966276778160587550497884091874841038381023829981332646698305710139768447010175537).isSome = true := by
  decide +kernel

theorem k4007_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).2 2).1 1).1
      75145181509003939323945760822233306190382617469505075193462854958125856313528366212328476211532418718751539).isSome = true := by
  decide +kernel

theorem k4007_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).2 2).1 1).2
      3975821487125329317941833085197358044334753808388702772804015823646095585186513671987).isSome = true := by
  decide +kernel

theorem k4007_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).2 2).2 3).1
      255300601584322065526646162576970391629000874998404573243909122124655009320437536943665).isSome = true := by
  decide +kernel

theorem k4007_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).1 3).2 2).2 3).2
      63658514145163585503466063667381373263068160968892206008441690363739986265951475440433).isSome = true := by
  decide +kernel

theorem k4007_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4007) 2).2 3).1 3).1
      77803422100987431058240961631356785488181659573585688335908901309189387495794507139559979002471497180947569862).isSome = true := by
  decide +kernel

theorem k4007_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4007) 2).2 3).1 3).2
      4967834373775461622294948194371453843671211143417959752107311094974781868217013069283377395548609684915023345862).isSome = true := by
  decide +kernel

theorem k4007_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).2 3).2 2).1 1).1
      4078803673095686105161061413586404997238668455034812563175704844860449609650729026419251).isSome = true := by
  decide +kernel

theorem k4007_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).2 3).2 2).1 1).2
      3977288723065500832980939627556088278128975938542871569940691324593807367920107214643).isSome = true := by
  decide +kernel

theorem k4007_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).2 3).2 2).2 1).1
      13813396704371771927940028320281979207632079160803872936252004846387).isSome = true := by
  decide +kernel

theorem k4007_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4007) 2).2 3).2 2).2 1).2
      215719691858492372889917017009112900810884000075140256094280110819).isSome = true := by
  decide +kernel

theorem k4008_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).1 3).1 2).1 3).1
      63418942165197163666114878461640764354439208881175163731899168366898254870449905834801).isSome = true := by
  decide +kernel

theorem k4008_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).1 3).1 2).1 3).2
      63253653039462980990618463190971306118195676693582007771505683984241894979077851421489).isSome = true := by
  decide +kernel

theorem k4008_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).1 3).1 2).2 3).1
      63463839997788950076992140703366542494634473776817783002099837911783114707645792623409).isSome = true := by
  decide +kernel

theorem k4008_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).1 3).1 2).2 3).2
      63297004208186286583792826057171609014887323332394500186256610485954910761811255597873).isSome = true := by
  decide +kernel

theorem k4008_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).1 3).2 2).1 3).1
      15778212262097169814042796640856866841230962186434071963829545205337682304009898122033).isSome = true := by
  decide +kernel

theorem k4008_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).1 3).2 2).1 3).2
      853629650261703763718524384930236203728759928830125318126398674737).isSome = true := by
  decide +kernel

theorem k4008_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).1 3).2 2).2 1).1
      252211336381540510628683541748415748324982509642673240011644666242448911000243074603827).isSome = true := by
  decide +kernel

theorem k4008_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).1 3).2 2).2 1).2
      3939443868043834049792953576905865066992287535299692316336744703937834615070437119795).isSome = true := by
  decide +kernel

theorem k4008_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).2 3).1 2).1 1).1
      1013819579613014137783711186989623589273409244303692216284669188239358682186966343981875).isSome = true := by
  decide +kernel

theorem k4008_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).2 3).1 2).1 1).2
      3958493365613247110687985008076752836845496771975722094965569885442616570178700007219).isSome = true := by
  decide +kernel

theorem k4008_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).2 3).1 2).2 1).1
      219953530835960240636203256261244683795829784219500068181019348839219).isSome = true := by
  decide +kernel

theorem k4008_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).2 3).1 2).2 1).2
      3960642303956725255958100310072295138826329292016669395791689265221336605297515779891).isSome = true := by
  decide +kernel

theorem k4008_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).2 3).2 2).1 1).1
      1010421569972962338693229213396477967914307722579826261704823182195631810009984765715404).isSome = true := by
  decide +kernel

theorem k4008_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).2 3).2 2).1 1).2
      3941671268193713031900845051418473098051673568273366449522923341074609602457260037939).isSome = true := by
  decide +kernel

theorem k4008_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).2 3).2 2).2 1).1
      3425094384457830960693369571954817236571095514024604741832649027276).isSome = true := by
  decide +kernel

theorem k4008_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4008) 2).2 3).2 2).2 1).2
      3943714397898157198615668020353271109245394360262016043945473162222242235235057620787).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4006 4009 :=
  (Cover.one (box := dirCellBox) (n := 4006)
      (.split 3 (.split 2 (.split 3 (.leaf _ k4006_0) (.leaf _ k4006_1)) (.leaf _ k4006_2)) (.split 2 (.split 3 (.leaf _ k4006_3) (.leaf _ k4006_4)) (.split 3 (.leaf _ k4006_5) (.leaf _ k4006_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4007)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k4007_0) (.leaf _ k4007_1)) (.split 3 (.leaf _ k4007_2) (.leaf _ k4007_3))) (.split 2 (.split 1 (.leaf _ k4007_4) (.leaf _ k4007_5)) (.split 3 (.leaf _ k4007_6) (.leaf _ k4007_7)))) (.split 3 (.split 3 (.leaf _ k4007_8) (.leaf _ k4007_9)) (.split 2 (.split 1 (.leaf _ k4007_10) (.leaf _ k4007_11)) (.split 1 (.leaf _ k4007_12) (.leaf _ k4007_13)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4008)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k4008_0) (.leaf _ k4008_1)) (.split 3 (.leaf _ k4008_2) (.leaf _ k4008_3))) (.split 2 (.split 3 (.leaf _ k4008_4) (.leaf _ k4008_5)) (.split 1 (.leaf _ k4008_6) (.leaf _ k4008_7)))) (.split 3 (.split 2 (.split 1 (.leaf _ k4008_8) (.leaf _ k4008_9)) (.split 1 (.leaf _ k4008_10) (.leaf _ k4008_11))) (.split 2 (.split 1 (.leaf _ k4008_12) (.leaf _ k4008_13)) (.split 1 (.leaf _ k4008_14) (.leaf _ k4008_15))))))

end C4.Cert.Dir128

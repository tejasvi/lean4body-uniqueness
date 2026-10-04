module

public import C4Check

public section

/-! Cells `2441 ≤ n < 2444` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir045

theorem k2441_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).1 3).1 1).1
      21983369514446424952068420703352777686660484404215491995128478640689119256871285178170191424749607870544449526385926714926136498).isSome = true := by
  decide +kernel

theorem k2441_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).1 3).1 1).2
      76257985980086193903503126712123651480511763125371003601239793845657338142996842835142270142798180669752471794).isSome = true := by
  decide +kernel

theorem k2441_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).1 3).2 1).1
      1189427000182247189989730315762832526456770008129472013288467078871694640871601717359328996968587435623300156).isSome = true := by
  decide +kernel

theorem k2441_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).1 3).2 1).2
      304550739661845824310197297148917010835161495750892529661397299302397091720740427626699870118802427990351474930).isSome = true := by
  decide +kernel

theorem k2441_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).2 3).1 1).1
      219021631910427960594528340298557936246759730821272119606446618409138).isSome = true := by
  decide +kernel

theorem k2441_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).2 3).1 1).2
      252485965111269413250637913593855619885992553255703312665992160305936422689086237045308).isSome = true := by
  decide +kernel

theorem k2441_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).2 3).2 1).1
      1162645896225757033242033028412135897983464757221405667321707488526991763616479244412294294228465603706028).isSome = true := by
  decide +kernel

theorem k2441_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).2 3).2 1).2
      218605712454986501550998403703351253503653706691810769068816260133436).isSome = true := by
  decide +kernel

theorem k2441_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 3).1 2).1 1).1
      16109062036024926017011004519086687776125920997312853959815329068159962158283241661288241).isSome = true := by
  decide +kernel

theorem k2441_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 3).1 2).1 1).2
      1005854637338192088665258114206719097758297227012916931147637318221880517626817236745276).isSome = true := by
  decide +kernel

theorem k2441_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 3).1 2).2 1).1
      15731869467256923444071783177806061995470762151595197325540194656621301065994846714940).isSome = true := by
  decide +kernel

theorem k2441_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 3).1 2).2 1).2
      15729864541706210388516737951262531487434061354546649625898627311405826860654090107964).isSome = true := by
  decide +kernel

theorem k2441_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 3).2 2).1 1).1
      3928583219588017781703744967314039390983493280722444676396130851399512249046962631628).isSome = true := by
  decide +kernel

theorem k2441_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 3).2 2).1 1).2
      15696843699094012179913482730100006783101158767868398966730784086451370851233796830156).isSome = true := by
  decide +kernel

theorem k2441_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 3).2 2).2 1).1
      3406434408031385023777603364047879439018482744402319386323585252412).isSome = true := by
  decide +kernel

theorem k2441_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 3).2 2).2 1).2
      13624155243826635387218133385976433906493869790255261852275588643900).isSome = true := by
  decide +kernel

theorem k2442_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).1 2).1 3).1 1).1
      212500810761493435020055815091380388598735129961379892990802734796).isSome = true := by
  decide +kernel

theorem k2442_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).1 2).1 3).1 1).2
      212473939273613710825886568172493431957697556760269011817191780044).isSome = true := by
  decide +kernel

theorem k2442_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).1 2).1 3).2 1).1
      849213287839294301139708836086099375361982596099990685532691582668).isSome = true := by
  decide +kernel

theorem k2442_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).1 2).1 3).2 1).2
      849126806247139910716745599055758570065114192781872578873010376396).isSome = true := by
  decide +kernel

theorem k2442_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).1 2).2 3).1 1).1
      184658085934310894103116678194050308623095753788).isSome = true := by
  decide +kernel

theorem k2442_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).1 2).2 3).1 1).2
      3402362055108433591066895238104663875494504276957375771499845958716).isSome = true := by
  decide +kernel

theorem k2442_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).1 2).2 3).2 1).1
      979848706052742616069042939242956039583855911892168531241785869934124390997200625356).isSome = true := by
  decide +kernel

theorem k2442_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).1 2).2 3).2 1).2
      979764533797845829060105041517095594117457471647288291395062838052785897839100059340).isSome = true := by
  decide +kernel

theorem k2442_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).2 2).1 3).1 1).1
      848526032293934470745410009902937834002232447541460973720327150284).isSome = true := by
  decide +kernel

theorem k2442_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).2 2).1 3).1 1).2
      212112550539697557915573264125632734707835927285204164267260500684).isSome = true := by
  decide +kernel

theorem k2442_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).2 2).1 3).2 1).1
      847776600486646022014506117519876676383163058389359731926546459340).isSome = true := by
  decide +kernel

theorem k2442_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).2 2).1 3).2 1).2
      847820842284355769528267802283736441928279057825401146290306800332).isSome = true := by
  decide +kernel

theorem k2442_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).2 2).2 1).1 3).1
      13265583140876636607155154795349102080032456763162285398012959436).isSome = true := by
  decide +kernel

theorem k2442_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).2 2).2 1).1 3).2
      13254999322090993632966008185634064339172891201841870453213731532).isSome = true := by
  decide +kernel

theorem k2442_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).2 2).2 1).2 3).1
      13264495289722561536839083492450967721241214996035402592033413836).isSome = true := by
  decide +kernel

theorem k2442_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2442) 3).2 2).2 1).2 3).2
      13254101316484551564926101530617575213385768344125105364121656012).isSome = true := by
  decide +kernel

theorem k2443_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2443) 3).1 2).1 1).1
      5573442908393293142061488209323756885280055154343393394766727388204258785813986147959662115836578721987959669049770911482376604467).isSome = true := by
  decide +kernel

theorem k2443_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2443) 3).1 2).1 1).2
      75563974824609537267662706824502457877799720965573029489805444511445105255460405097580316539301516964975307570).isSome = true := by
  decide +kernel

theorem k2443_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2443) 3).1 2).2 1).1
      25749639390434522078063080300408676101097251327092678058352372854504333000382131244696692095504544608147498247381615150256585810922511447444497427148).isSome = true := by
  decide +kernel

theorem k2443_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2443) 3).1 2).2 1).2
      348621098283497807032773845994249811707360990412431925604010454047428856313157217926033937134922196482560087908935018542175566540).isSome = true := by
  decide +kernel

theorem k2443_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2443) 3).2 2).1 1).1
      15977484042742907314882617742132754858566264770938843285205959809130478733835706333252403).isSome = true := by
  decide +kernel

theorem k2443_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2443) 3).2 2).1 1).2
      4607007240750500285213744324504267671177224047015058069130413728201742081691508983186958112131339288694476).isSome = true := by
  decide +kernel

theorem k2443_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2443) 3).2 2).2 1).1
      18434886173460267646960822546616759127304752653931250450131691241598342820659311604990350332225922401290956).isSome = true := by
  decide +kernel

theorem k2443_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2443) 3).2 2).2 1).2
      255866582461511248794771506150144806413970505877649112562572085917342154195858373518940978).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2441 2444 :=
  (Cover.one (box := dirCellBox) (n := 2441)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2441_0) (.leaf _ k2441_1)) (.split 1 (.leaf _ k2441_2) (.leaf _ k2441_3))) (.split 3 (.split 1 (.leaf _ k2441_4) (.leaf _ k2441_5)) (.split 1 (.leaf _ k2441_6) (.leaf _ k2441_7)))) (.split 3 (.split 2 (.split 1 (.leaf _ k2441_8) (.leaf _ k2441_9)) (.split 1 (.leaf _ k2441_10) (.leaf _ k2441_11))) (.split 2 (.split 1 (.leaf _ k2441_12) (.leaf _ k2441_13)) (.split 1 (.leaf _ k2441_14) (.leaf _ k2441_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2442)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2442_0) (.leaf _ k2442_1)) (.split 1 (.leaf _ k2442_2) (.leaf _ k2442_3))) (.split 3 (.split 1 (.leaf _ k2442_4) (.leaf _ k2442_5)) (.split 1 (.leaf _ k2442_6) (.leaf _ k2442_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k2442_8) (.leaf _ k2442_9)) (.split 1 (.leaf _ k2442_10) (.leaf _ k2442_11))) (.split 1 (.split 3 (.leaf _ k2442_12) (.leaf _ k2442_13)) (.split 3 (.leaf _ k2442_14) (.leaf _ k2442_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2443)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2443_0) (.leaf _ k2443_1)) (.split 1 (.leaf _ k2443_2) (.leaf _ k2443_3))) (.split 2 (.split 1 (.leaf _ k2443_4) (.leaf _ k2443_5)) (.split 1 (.leaf _ k2443_6) (.leaf _ k2443_7)))))

end C4.Cert.Dir045

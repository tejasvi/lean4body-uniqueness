module

public import C4Check

public section

/-! Cells `3977 ≤ n < 3980` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir126

theorem k3977_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3977) 3).1
      279011).isSome = true := by
  decide +kernel

theorem k3977_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3977) 3).2 3).1
      117446434624447872873003668978585412926293757637424805210072586606708557974187484974130144794673409988284175511227620537074181440663186674369879317834515566).isSome = true := by
  decide +kernel

theorem k3977_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3977) 3).2 3).2 2).1
      12850208983291287297344585575352064223189266601997303044911107339622946683270760373233481355757867395463197317165972164683998810918).isSome = true := by
  decide +kernel

theorem k3977_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3977) 3).2 3).2 2).2
      22848171000268212726292825778789369318328045571238778490914347083252407043348459344252409621622455267474084055520689024726473).isSome = true := by
  decide +kernel

theorem k3978_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).1 2).1 3).1
      822121207517960735486817369369387742912432568908986333169845064268606768567633105861550551592320107909524222903673065227938874102566).isSome = true := by
  decide +kernel

theorem k3978_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3978) 3).1 2).1 3).2 2).1
      16382686105695726898847671374609600597975383724255590701496508749682982631048496682885).isSome = true := by
  decide +kernel

theorem k3978_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3978) 3).1 2).1 3).2 2).2
      261857298995141731227068362476739452185835231460857819214580615630624092573520847919749).isSome = true := by
  decide +kernel

theorem k3978_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).1 2).2 3).1
      20043276671116632306143804077742861919206223413262203134767129316173060795379762881717580882993441961238352585).isSome = true := by
  decide +kernel

theorem k3978_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).1 2).2 3).2
      23380913964369178061782902982536400742491933043297843850350585686935403447613728791570816623950034482516902181567025512263951670470).isSome = true := by
  decide +kernel

theorem k3978_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).1 2).1 3).1
      4796057299540758598185047800020816591759594835985278526204290332810818038703055989707703604859797644401861).isSome = true := by
  decide +kernel

theorem k3978_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).1 2).1 3).2
      4760388014145709784189948684732177838519423206539165095394809190818445707465299940965958558220217717513413).isSome = true := by
  decide +kernel

theorem k3978_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).1 2).2 3).1
      19224158015515624181312986878418172785344485622668827734771021151995667275251853526455986015761534463463217).isSome = true := by
  decide +kernel

theorem k3978_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).1 2).2 3).2
      351716856342368283213697268287931874720773302294829902972504198043540214836823578543375493164251176024965109303262613509463857).isSome = true := by
  decide +kernel

theorem k3978_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).2 3).1 2).1
      260460814903392512341937789202220405311280563230719691433902046488536629940174947014277).isSome = true := by
  decide +kernel

theorem k3978_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).2 3).1 2).2
      220356226761947745767899857578547457999889411833925230192066041649).isSome = true := by
  decide +kernel

theorem k3978_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).2 3).2 2).1
      4770265480360899404193575129013927351578091651233739639266625717266772647229968048050483253439935309798193).isSome = true := by
  decide +kernel

theorem k3978_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).2 3).2 2).2
      258805686948230018219621907946824065289170241797659698533227952902647684211163691521669).isSome = true := by
  decide +kernel

theorem k3979_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).1 2).1 3).1
      4735706457528658739666191155771372543359448542434693745273268610691103185723463993447760115651256564669637).isSome = true := by
  decide +kernel

theorem k3979_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).1 2).1 3).2
      4711838389439677038143676634441391582439018142393001539202979568577786484007706425703944000283737586621637).isSome = true := by
  decide +kernel

theorem k3979_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).1 2).2 3).1
      1399665063938850775970532019864813252489947485200905697927475406172245147620739429336161151028983925090291172752996129134443313).isSome = true := by
  decide +kernel

theorem k3979_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).1 2).2 3).2
      1392598772450870583527641503608007483696984410869630615568376802578497223232046104165400034451869283080063819123660039680523057).isSome = true := by
  decide +kernel

theorem k3979_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).2 2).1 3).1
      1173071244712435791088426184029666523603559017402423542876270746351631556114351104201787833960097095245445).isSome = true := by
  decide +kernel

theorem k3979_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).2 2).1 3).2
      63374960045310984461405270591283761337897974459012172141414948396741987730975575347913).isSome = true := by
  decide +kernel

theorem k3979_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).2 2).2 3).1
      346683986867698132469488977542265388862242143005219124083892059413116957056905206253284173709583718553787417164151774189674289).isSome = true := by
  decide +kernel

theorem k3979_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).2 2).2 3).2
      36822404238786451591845779499180414416610493754475904282599877867157565189019909518286021).isSome = true := by
  decide +kernel

theorem k3979_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).2 3).1 2).1 3).1
      18962319035790279931573307523043078217326289961492430389658550941398823949255793883652334646223232817290033).isSome = true := by
  decide +kernel

theorem k3979_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).2 3).1 2).1 3).2
      75540525095314656701471525272335283129748265339500111636411705303639168974524571156003543035847561992170289).isSome = true := by
  decide +kernel

theorem k3979_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).2 3).1 2).2 3).1
      257278672981613807108426054519087335006260369904350236926450245749238227225242434037385).isSome = true := by
  decide +kernel

theorem k3979_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).2 3).1 2).2 3).2
      4722270513815800929611896423201294654785626834039514280286350437849945442639105806275923372610211636697905).isSome = true := by
  decide +kernel

theorem k3979_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).2 3).2 2).1 3).1
      75223018243607181397253174964953128721171927349782533287950178892319971371436771114773200972508590568336177).isSome = true := by
  decide +kernel

theorem k3979_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).2 3).2 2).1 3).2
      1015867536861912678486006921641273224628565593717858810604901230198743878148875785497393).isSome = true := by
  decide +kernel

theorem k3979_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).2 3).2 2).2 3).1
      4706799854478755131869014518672309019067835591447871605136900673991909248982350463394365398774606223235889).isSome = true := by
  decide +kernel

theorem k3979_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3979) 2).2 3).2 2).2 3).2
      63561030058942178166917133914233744854506243987386941969760122325520819292059041897265).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3977 3980 :=
  (Cover.one (box := dirCellBox) (n := 3977)
      (.split 3 (.leaf _ k3977_0) (.split 3 (.leaf _ k3977_1) (.split 2 (.leaf _ k3977_2) (.leaf _ k3977_3))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3978)
      (.split 3 (.split 2 (.split 3 (.leaf _ k3978_0) (.split 2 (.leaf _ k3978_1) (.leaf _ k3978_2))) (.split 3 (.leaf _ k3978_3) (.leaf _ k3978_4))) (.split 2 (.split 2 (.split 3 (.leaf _ k3978_5) (.leaf _ k3978_6)) (.split 3 (.leaf _ k3978_7) (.leaf _ k3978_8))) (.split 3 (.split 2 (.leaf _ k3978_9) (.leaf _ k3978_10)) (.split 2 (.leaf _ k3978_11) (.leaf _ k3978_12)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3979)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3979_0) (.leaf _ k3979_1)) (.split 3 (.leaf _ k3979_2) (.leaf _ k3979_3))) (.split 2 (.split 3 (.leaf _ k3979_4) (.leaf _ k3979_5)) (.split 3 (.leaf _ k3979_6) (.leaf _ k3979_7)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3979_8) (.leaf _ k3979_9)) (.split 3 (.leaf _ k3979_10) (.leaf _ k3979_11))) (.split 2 (.split 3 (.leaf _ k3979_12) (.leaf _ k3979_13)) (.split 3 (.leaf _ k3979_14) (.leaf _ k3979_15))))))

end C4.Cert.Dir126

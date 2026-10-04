module

public import C4Check

public section

/-! Cells `2524 ≤ n < 2532` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir050

theorem k2524_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2524) 3).1 2).1
      1598537535488203099814899564022901129222417084978502006754342404689007565516128806423992470770582611506332720137421081243473046758635765907482445).isSome = true := by
  decide +kernel

theorem k2524_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2524) 3).1 2).2
      15541042978119154526399263201951127799312030672018794736212097571086693397834743153).isSome = true := by
  decide +kernel

theorem k2524_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2524) 3).2 2).1 1).1
      15480907617384205405261499484220520832234377734042570641085202369586841602117432764).isSome = true := by
  decide +kernel

theorem k2524_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2524) 3).2 2).1 1).2
      61944865794514866850524970961573588152969442300898898980082731880748597829832136508).isSome = true := by
  decide +kernel

theorem k2524_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2524) 3).2 2).2
      6370325990872960625455214118100829346515251497600734868391257569381283096854091384439562004633250986391203626809280091463065136733145487885563377).isSome = true := by
  decide +kernel

theorem k2525_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2525) 3).1 2).1 1).1
      987555020588677457200755264146797488409867002076944375224032030630079764652354950972).isSome = true := by
  decide +kernel

theorem k2525_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2525) 3).1 2).1 1).2
      856485627588481059286663128626917783935735368986837851867323517756).isSome = true := by
  decide +kernel

theorem k2525_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2525) 3).1 2).2
      1409431607761506785610713483752135478588900037436387767335174444012214432410900985686859206336141759795358013782362734005999590641).isSome = true := by
  decide +kernel

theorem k2525_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2525) 3).2 2).1 1).1
      213493438479639670867307437967402022918708800408228753296465021756).isSome = true := by
  decide +kernel

theorem k2525_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2525) 3).2 2).1 1).2
      213497306547419543396700505667549037350152434400067824795271027260).isSome = true := by
  decide +kernel

theorem k2525_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2525) 3).2 2).2 1).1
      854060529357712827772948278316240965997994813055940278714770606908).isSome = true := by
  decide +kernel

theorem k2525_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2525) 3).2 2).2 1).2
      53381449063137281444777290146454768181506115724933674688980579900).isSome = true := by
  decide +kernel

theorem k2526_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2526) 3).1 2).1 1).1
      53250876421767527113056449449698900859157827161393977901418149436).isSome = true := by
  decide +kernel

theorem k2526_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2526) 3).1 2).1 1).2
      3407617674669004063243527908897508214035190511632610174747491158588).isSome = true := by
  decide +kernel

theorem k2526_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2526) 3).1 2).2
      4864128740668743629895601367788934405606910656055473432737361288098656437240041013382282699815293958164407900401).isSome = true := by
  decide +kernel

theorem k2526_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2526) 3).2 2).1 1).1
      46114297890525431641272052652128362040982434364).isSome = true := by
  decide +kernel

theorem k2526_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2526) 3).2 2).1 1).2
      250971893111074770003906595951043554961257451471848456617078677052505605016426554847804).isSome = true := by
  decide +kernel

theorem k2526_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2526) 3).2 2).2
      19420698012954524050353736182846989624760099377716260555263569619376275483048901440031065542530696098114839234801).isSome = true := by
  decide +kernel

theorem k2527_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2527) 3).1 2).1 1).1
      15659763048377736510601325298058025776929328022663779668153893634067334875424912948284).isSome = true := by
  decide +kernel

theorem k2527_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2527) 3).1 2).1 1).2
      15660056342502928494631674639168362720932936313387354525552872388272761514235755609148).isSome = true := by
  decide +kernel

theorem k2527_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2527) 3).1 2).2 1).1
      53063999550962083208555244895182104856543035490371703638560455740).isSome = true := by
  decide +kernel

theorem k2527_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2527) 3).1 2).2 1).2
      3396204759711783133617385438783330879799167936131592434806368877628).isSome = true := by
  decide +kernel

theorem k2527_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2527) 3).2 2).1 1).1
      847774736581939406516546823931571730757734390070178622110736792636).isSome = true := by
  decide +kernel

theorem k2527_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2527) 3).2 2).1 1).2
      847792093160568714037838438105899753670851848999736443898554694716).isSome = true := by
  decide +kernel

theorem k2527_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2527) 3).2 2).2
      22347264478879960648560194885645281365945716184971857119170714361887822256042750347013526385127358577599339203237223218584334285884).isSome = true := by
  decide +kernel

theorem k2528_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2528) 3).1 2).1 1).1
      2869010014791551775144592605317968178071444172).isSome = true := by
  decide +kernel

theorem k2528_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2528) 3).1 2).1 1).2
      846814089324612902006969981027779999308622698613539682955488017468).isSome = true := by
  decide +kernel

theorem k2528_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2528) 3).1 2).2 1).1
      2869441047542058601133987403650874102837259324).isSome = true := by
  decide +kernel

theorem k2528_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2528) 3).1 2).2 1).2
      45913140692423892012173203412500918533116017724).isSome = true := by
  decide +kernel

theorem k2528_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2528) 3).2 2).1 1).1
      183434070269169488612833493152202954024549131212).isSome = true := by
  decide +kernel

theorem k2528_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2528) 3).2 2).1 1).2
      183440418917292945753787392282048947173434631116).isSome = true := by
  decide +kernel

theorem k2528_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2528) 3).2 2).2
      22279384494163135428642714969447531429305494400650116821991211486460921571561919054834152733548589578635462360327096704837480037436).isSome = true := by
  decide +kernel

theorem k2529_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2529) 3).1 2).1
      18853225835499252742843722226970038917503011338335955772783109526940698933743953050378386349253001126842350652).isSome = true := by
  decide +kernel

theorem k2529_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2529) 3).1 2).2
      86960405527812264934689739209085456396739214269807668793387419197980008285986329075599945227944883333727075100263877125686836284).isSome = true := by
  decide +kernel

theorem k2529_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2529) 3).2 1).1
      4089553624595218634465264220653148876879172264880388990934634535970696532488737786122150860).isSome = true := by
  decide +kernel

theorem k2529_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2529) 3).2 1).2
      301486835767279823763446234795073238480261807097177508654340598063954786180565460078469482839816576479842679868).isSome = true := by
  decide +kernel

theorem k2530_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2530) 3).1 1).1
      255206778639485232423985118956352067238725444279137761680361381516471478404859479375946700).isSome = true := by
  decide +kernel

theorem k2530_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2530) 3).1 1).2
      4087640245611056580888905648662858860615361407823537923058754782659811239576895255450106940).isSome = true := by
  decide +kernel

theorem k2530_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2530) 3).2 1).1
      249119875297955748957078373439760469108281700665572008268501733542494760466548766221260).isSome = true := by
  decide +kernel

theorem k2530_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2530) 3).2 1).2
      15944215563810469446440907123004829245384275767976526279409553948118362730519968765387724).isSome = true := by
  decide +kernel

theorem k2531_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2531) 3).1 1).1
      210918845578461638168619604654165384590423427523657713412438739660).isSome = true := by
  decide +kernel

theorem k2531_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2531) 3).1 1).2
      844176102403780345325122154165205839041395179607567062220381561804).isSome = true := by
  decide +kernel

theorem k2531_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2531) 3).2 1).1
      843382373874249803080870712496918756681697770438345844213998889676).isSome = true := by
  decide +kernel

theorem k2531_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2531) 3).2 1).2
      210869325522871276935914617509561990037235588962398330286352353996).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2524 2532 :=
  (Cover.one (box := dirCellBox) (n := 2524)
      (.split 3 (.split 2 (.leaf _ k2524_0) (.leaf _ k2524_1)) (.split 2 (.split 1 (.leaf _ k2524_2) (.leaf _ k2524_3)) (.leaf _ k2524_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2525)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2525_0) (.leaf _ k2525_1)) (.leaf _ k2525_2)) (.split 2 (.split 1 (.leaf _ k2525_3) (.leaf _ k2525_4)) (.split 1 (.leaf _ k2525_5) (.leaf _ k2525_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2526)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2526_0) (.leaf _ k2526_1)) (.leaf _ k2526_2)) (.split 2 (.split 1 (.leaf _ k2526_3) (.leaf _ k2526_4)) (.leaf _ k2526_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2527)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2527_0) (.leaf _ k2527_1)) (.split 1 (.leaf _ k2527_2) (.leaf _ k2527_3))) (.split 2 (.split 1 (.leaf _ k2527_4) (.leaf _ k2527_5)) (.leaf _ k2527_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2528)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2528_0) (.leaf _ k2528_1)) (.split 1 (.leaf _ k2528_2) (.leaf _ k2528_3))) (.split 2 (.split 1 (.leaf _ k2528_4) (.leaf _ k2528_5)) (.leaf _ k2528_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2529)
      (.split 3 (.split 2 (.leaf _ k2529_0) (.leaf _ k2529_1)) (.split 1 (.leaf _ k2529_2) (.leaf _ k2529_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2530)
      (.split 3 (.split 1 (.leaf _ k2530_0) (.leaf _ k2530_1)) (.split 1 (.leaf _ k2530_2) (.leaf _ k2530_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2531)
      (.split 3 (.split 1 (.leaf _ k2531_0) (.leaf _ k2531_1)) (.split 1 (.leaf _ k2531_2) (.leaf _ k2531_3))))

end C4.Cert.Dir050

module

public import C4Check

public section

/-! Cells `570 ≤ n < 847` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir001

theorem c0 : allCells dirCell 570 597 [
    44556090355202632764953295702896342060889350, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    86801797284708913967275170009744211529524988077546697069626559284523590285022155431447931110024731695143444204845544530548346951] = true := by
  decide +kernel

theorem c1 : allCells dirCell 597 598 [
    102298441334073022275596878515441853842233605002109158151557716367620354699331275933757472015338376686373722337887762321841153008704383045908031161639] = true := by
  decide +kernel

theorem c2 : allCells dirCell 598 625 [
    2362269710104038592577, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0,
    1148485696978694656998312354248358790453862879451354462413392359009465079761890262971811209930204950896903] = true := by
  decide +kernel

theorem c3 : allCells dirCell 625 626 [
    1598511793838887594644107702420269732988186534835919047129388306251903654354396698526018123977726507706987785223855587218971884763409020649280079309] = true := by
  decide +kernel

theorem c4 : allCells dirCell 626 653 [
    2358868485233341569089, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 3891476506584386069018656212927784377022975581242005816379750129055934689174342070535] = true := by
  decide +kernel

theorem c5 : allCells dirCell 653 680 [
    338467262397262839049152893600938137420163682776696527656446288640529887547229140375834475724573093613499873799049996495403589,
    2358935958963829388097, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0] = true := by
  decide +kernel

theorem c6 : allCells dirCell 680 681 [
    972905785245609984583566205356220739730617498618455333786866149570235617491238686983] = true := by
  decide +kernel

theorem c7 : allCells dirCell 681 708 [
    71672552862234865871042594853065042616227631831921544561981912521814310122406535863431530224835192153929,
    2359007531673538723393, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0] = true := by
  decide +kernel

theorem c8 : allCells dirCell 708 709 [
    972846104374572199412254710992111965154420708103344807246263239350580759494913474823] = true := by
  decide +kernel

theorem c9 : allCells dirCell 709 736 [
    71672154700907736029196176184179646223589484820094579921152539121030568077012844621896920417032475890757,
    2359079712413093096513, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0] = true := by
  decide +kernel

theorem c10 : allCells dirCell 736 737 [
    972789881435240456075708579875700393985425039861212399210839842453571923994583478535] = true := by
  decide +kernel

theorem c11 : allCells dirCell 737 764 [
    71671940701711171112011018260807689744037154656306364339140077468996676517179945507005283023763425590853,
    2359150489076240537921, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0] = true := by
  decide +kernel

theorem c12 : allCells dirCell 764 765 [
    972737176132917154966205441174862896756156662175586814964468072181773729513108530445] = true := by
  decide +kernel

theorem c13 : allCells dirCell 765 791 [
    71671847218906969344906836833723704300082838778297336302566226227108349492416497747704754366885431689285,
    2359218756653812741697, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k791_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 791) 2).1 2).1
      15577868419906011574956482180007013470824137252180410146161338729009205020897490163463).isSome = true := by
  decide +kernel

theorem k791_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 791) 2).1 2).2
      4598786149121174306752832791736429409377196538853859963157970881877169210608361707598706807577087984310023).isSome = true := by
  decide +kernel

theorem k791_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 791) 2).2 3).1
      3380687238472178773863175754626751930308396753159340482420401952518).isSome = true := by
  decide +kernel

theorem k791_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 791) 2).2 3).2
      1389563774597770294141879442380690223914568418218027567776862298142745611696403617517951041013975674614771620080167066603616560182).isSome = true := by
  decide +kernel

theorem k792_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 792) 2).1
      44818976730808167552714069124598603449179174231452136024917663793712923708984120841599189342).isSome = true := by
  decide +kernel

theorem k792_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 792) 2).2 2).1
      25007186702746009344902373795805011726218013252677635038877169914690059774320423353620562209881326411912872205043172301630276646522675838108459319).isSome = true := by
  decide +kernel

theorem k792_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 792) 2).2 2).2 3).1
      3893073270396200615104429698899502461302531698142823500912536713074947417708074730309).isSome = true := by
  decide +kernel

theorem k792_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 792) 2).2 2).2 3).2
      243242556561165889909387271461983048545174875740768906241697253944323722582933116721).isSome = true := by
  decide +kernel

theorem k793_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 793) 2).1
      65906).isSome = true := by
  decide +kernel

theorem k793_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 793) 2).2 2).1
      2468462399366027187703922279699785135383221501903669233533478983).isSome = true := by
  decide +kernel

theorem k793_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 793) 2).2 2).2
      21165432111960179481129741184381303378566388613043607197987996225246616478874145333573467342650547456025107972155067388429767).isSome = true := by
  decide +kernel

theorem c17 : allCells dirCell 794 819 [
    3978097981346508770424097338507203089264562632174262132832749936698194705464790415245666, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k819_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 819) 2).1 3).1
      2931873554604473435999955439003933794231152083910).isSome = true := by
  decide +kernel

theorem k819_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 819) 2).1 3).2
      410185185533132268346829996382509396009502525022984790469127668289384116879325522322941579463733433066213260401367135200016153303875115137311904551990).isSome = true := by
  decide +kernel

theorem k819_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 819) 2).2
      1459855179026422175805317200385350099285588707390510213629793858653013840758081133828790354475167380230105128963606950214007691284595655).isSome = true := by
  decide +kernel

theorem k820_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 820) 2).1 3).1 2).1
      15573239001661646473404169346400720527872538268351211613654724077571990268007480977485).isSome = true := by
  decide +kernel

theorem k820_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 820) 2).1 3).1 2).2
      15574566796818866430756276784795166452146566949064122417138560668628766343073024884301).isSome = true := by
  decide +kernel

theorem k820_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 820) 2).1 3).2 2).1
      52725825941676075690062122982882446084190790287799071224525133617).isSome = true := by
  decide +kernel

theorem k820_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 820) 2).1 3).2 2).2
      15584293129677171929841873175126670163637914884738617935337986841082980155556155055329).isSome = true := by
  decide +kernel

theorem k820_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 820) 2).2 3).1 1).1
      15568444724344062928747202902541590760865816110323526065570033153015628860442531552327).isSome = true := by
  decide +kernel

theorem k820_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 820) 2).2 3).1 1).2
      249146445412160072630489392823687691988632445662257948896920962520178227308929348664718).isSome = true := by
  decide +kernel

theorem k820_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 820) 2).2 3).2 1).1
      62242339289858470183370977144936281281101526157483510374562196904750758144436206787810).isSome = true := by
  decide +kernel

theorem k820_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 820) 2).2 3).2 1).2
      996251075351362797952195210188828138120883500563674911593168626511300129872106839962418).isSome = true := by
  decide +kernel

theorem k821_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 821) 2).1 3).1
      1019460094589861249158295464133050984869027624870012806585512525030810127088407214024217485).isSome = true := by
  decide +kernel

theorem k821_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 821) 2).1 3).2
      1174993267570046260129088948248453385329970703738572706556440169363896015411592650321497200925710497578648777).isSome = true := by
  decide +kernel

theorem k821_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 821) 2).2 3).1 1).1
      62228194186135503275678534133137240431487533138955180003607126710196075953365315443937).isSome = true := by
  decide +kernel

theorem k821_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 821) 2).2 3).1 1).2
      3373926299321225282637688414202247640813058527234191208425632355122).isSome = true := by
  decide +kernel

theorem k821_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 821) 2).2 3).2
      4812694100102033068958909362538427956833793918630852941356988983076757778096936288530467078706786368925208761225).isSome = true := by
  decide +kernel

theorem k822_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 822) 2).1 2).1
      71671230652118620831121148201282331587665721527308971521035600704428464006901256033123343980482346796487).isSome = true := by
  decide +kernel

theorem k822_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 822) 2).1 2).2
      62171262371121223054745422087133957092464955896281482427458864334038570284528085640391).isSome = true := by
  decide +kernel

theorem k822_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 822) 2).2 3).1
      3979975389832024544428086516348980195041285042860901118862741348080497923397431736816841).isSome = true := by
  decide +kernel

theorem k822_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 822) 2).2 3).2
      822875882656679709133810958718447826600285635981592364915821777).isSome = true := by
  decide +kernel

theorem c22 : allCells dirCell 823 847 [
    3449220954220984938737827401445587527083696484956565059617168888447258, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 570 847 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13).trans <|
  (Cover.one (box := dirCellBox) (n := 791)
      (.split 2 (.split 2 (.leaf _ k791_0) (.leaf _ k791_1)) (.split 3 (.leaf _ k791_2) (.leaf _ k791_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 792)
      (.split 2 (.leaf _ k792_0) (.split 2 (.leaf _ k792_1) (.split 3 (.leaf _ k792_2) (.leaf _ k792_3))))).trans <|
  (Cover.one (box := dirCellBox) (n := 793)
      (.split 2 (.leaf _ k793_0) (.split 2 (.leaf _ k793_1) (.leaf _ k793_2)))).trans <|
  (Cover.dir c17).trans <|
  (Cover.one (box := dirCellBox) (n := 819)
      (.split 2 (.split 3 (.leaf _ k819_0) (.leaf _ k819_1)) (.leaf _ k819_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 820)
      (.split 2 (.split 3 (.split 2 (.leaf _ k820_0) (.leaf _ k820_1)) (.split 2 (.leaf _ k820_2) (.leaf _ k820_3))) (.split 3 (.split 1 (.leaf _ k820_4) (.leaf _ k820_5)) (.split 1 (.leaf _ k820_6) (.leaf _ k820_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 821)
      (.split 2 (.split 3 (.leaf _ k821_0) (.leaf _ k821_1)) (.split 3 (.split 1 (.leaf _ k821_2) (.leaf _ k821_3)) (.leaf _ k821_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 822)
      (.split 2 (.split 2 (.leaf _ k822_0) (.leaf _ k822_1)) (.split 3 (.leaf _ k822_2) (.leaf _ k822_3)))).trans <|
  (Cover.dir c22)

end C4.Cert.Dir001

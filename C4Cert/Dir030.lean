module

public import C4Check

public section

/-! Cells `2135 ≤ n < 2164` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir030

theorem k2135_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2135) 3).1 2).1
      5587257790322187864274574003728972390781721108524394672457765723716896276149891543990172424201975853886827918998249320159121895665).isSome = true := by
  decide +kernel

theorem k2135_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2135) 3).1 2).2
      1397066434498475397118603594198771122777733624294086260227017936634431685325946327094051179778758987080942822805465882711671828721).isSome = true := by
  decide +kernel

theorem k2135_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2135) 3).2 2).1
      4197259210695161359218242142086042854665291237642927651126253132695226379303253943997204590833).isSome = true := by
  decide +kernel

theorem k2135_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2135) 3).2 2).2
      65655370529625771532664293672191102819014748057027181911284374645549871369069178732607107313).isSome = true := by
  decide +kernel

theorem k2136_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2136) 3).1 2).1
      302122574293851790736573246283553465601547392226972319389716464383438527443493527175803091816495218912630790961).isSome = true := by
  decide +kernel

theorem k2136_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2136) 3).1 2).2
      16380238414203897727863912113988226701554757801233291521761662279811983679785602946131680049).isSome = true := by
  decide +kernel

theorem k2136_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2136) 3).2 2).1
      89175149004301419006641098444342897629073830222298895016543929583614412331383566150064048969581475305174629213099412367040689945660).isSome = true := by
  decide +kernel

theorem k2136_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2136) 3).2 2).2
      348061525219756596613837906756872045246833543980766332162572327409331027336197008116657216684018194178625099350282980457939418172).isSome = true := by
  decide +kernel

theorem k2137_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2137) 3).1 2).1
      22254841861705039610086871469659752071152480472464298857853491056414842868247864181373116769573025079527951139849757575481297353788).isSome = true := by
  decide +kernel

theorem k2137_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2137) 3).1 2).2
      75407960155374803491752806712719016024305794087345175837737900587469196979994980263747317434709754034917096508).isSome = true := by
  decide +kernel

theorem k2137_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2137) 3).2 1).1
      1022131478228058972103694648194223168690198289941559230739679302325477780786131538311581490).isSome = true := by
  decide +kernel

theorem k2137_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2137) 3).2 1).2
      4709918864636694964072252108726997927828708015741510187087393484575357618959175679939104002734249260730794956).isSome = true := by
  decide +kernel

theorem k2138_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2138) 3).1 2).1
      63788505373981198366039693080667231796280698585005104207560155219530299685453131129670449).isSome = true := by
  decide +kernel

theorem k2138_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2138) 3).1 2).2
      864535219427102645974741719943255203187142744403139804440782413904956).isSome = true := by
  decide +kernel

theorem k2138_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2138) 3).2 1).1
      3378423566545636348482651672466052135877245752463138087077877893836).isSome = true := by
  decide +kernel

theorem k2138_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2138) 3).2 1).2
      249088122443867244410344624147498753853901971660968599693017077385388894522961207216844).isSome = true := by
  decide +kernel

theorem k2139_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2139) 3).1 1).1
      3889894475450187974384469538641559842535765347834523938027049351270331743491707099852).isSome = true := by
  decide +kernel

theorem k2139_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2139) 3).1 1).2
      210890660018552020888835119855301366751468421329792483808853347020).isSome = true := by
  decide +kernel

theorem k2139_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2139) 3).2
      5423464181566721253121434828429710817714716440885283935985322466111866082426760564027573031156101554480518370515875626758822705).isSome = true := by
  decide +kernel

theorem k2140_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2140) 3).1
      5419094659209591285980153623854378108065793811071613342525187804047609971963625971848543389742441802757858601652144138873068337).isSome = true := by
  decide +kernel

theorem k2140_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2140) 3).2
      62192099592296153916708457803724150009340122793586774656910757981754732268244522523825).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 2141 2142 [
    399609073818376169968873055211391707917795050261602943708630936127045901091728335286486984077755810097025267399970247449278160066655509868384630215] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2142 2161 [
    2360628952881192469057, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1668260537836224384186308660381311428665221841776724523714500286443799407686667156899335483807320834170622733346159239214096286355789333617188441440347] = true := by
  decide +kernel

theorem k2161_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2161) 3).1 2).1
      25371116643300220126920300846320793104419497527006410362360122195708676851369123013778740738384075623320611418800262430475936942678408446002165235).isSome = true := by
  decide +kernel

theorem k2161_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2161) 3).1 2).2
      15421777055519953699708595099782524579237867956193926331469030345651552444092385649).isSome = true := by
  decide +kernel

theorem k2161_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2161) 3).2 2).1
      343104701060040419148486552101521630223683501888549584025740619782617114857762907815113645281906244169608933448759066014348785).isSome = true := by
  decide +kernel

theorem k2161_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2161) 3).2 2).2
      74398081458774916245817030609749262311816895184169131895805699961319012676255940953173379750113750842635761).isSome = true := by
  decide +kernel

theorem k2162_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2162) 3).1 2).1
      19002284583929736659625357945381928570748538032787851484106755772181777365758682100074946831734941915576169713).isSome = true := by
  decide +kernel

theorem k2162_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2162) 3).1 2).2
      16095755705691692585064286732701811024743947237440586496994905968840357926306063755408625).isSome = true := by
  decide +kernel

theorem k2162_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2162) 3).2 2).1
      18964878423262841369064889743444104391448790502340319668473198101920173734117230784663824182612669518331556668).isSome = true := by
  decide +kernel

theorem k2162_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2162) 3).2 2).2
      296350222374727295504510475246853533403137273951300464234536772586890429261278259162133930101118465822018364).isSome = true := by
  decide +kernel

theorem k2163_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2163) 3).1 2).1
      1183992778492982177995443516078324627439920876740039475813824713605486726834219566397871816525969773891101500).isSome = true := by
  decide +kernel

theorem k2163_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2163) 3).1 2).2
      295859995920304894160727944987329403970503906623198565574063169354504975769137523793443185527553930961920828).isSome = true := by
  decide +kernel

theorem k2163_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2163) 3).2 2).1
      18909001533900842359671918894103723557865457744004161549331193152344100870547770602397267813549796937508307772).isSome = true := by
  decide +kernel

theorem k2163_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2163) 3).2 2).2
      64069139511331130644696647558811535113621606680783735674805774734683413761498135607100220).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2135 2164 :=
  (Cover.one (box := dirCellBox) (n := 2135)
      (.split 3 (.split 2 (.leaf _ k2135_0) (.leaf _ k2135_1)) (.split 2 (.leaf _ k2135_2) (.leaf _ k2135_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2136)
      (.split 3 (.split 2 (.leaf _ k2136_0) (.leaf _ k2136_1)) (.split 2 (.leaf _ k2136_2) (.leaf _ k2136_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2137)
      (.split 3 (.split 2 (.leaf _ k2137_0) (.leaf _ k2137_1)) (.split 1 (.leaf _ k2137_2) (.leaf _ k2137_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2138)
      (.split 3 (.split 2 (.leaf _ k2138_0) (.leaf _ k2138_1)) (.split 1 (.leaf _ k2138_2) (.leaf _ k2138_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2139)
      (.split 3 (.split 1 (.leaf _ k2139_0) (.leaf _ k2139_1)) (.leaf _ k2139_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2140)
      (.split 3 (.leaf _ k2140_0) (.leaf _ k2140_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 2161)
      (.split 3 (.split 2 (.leaf _ k2161_0) (.leaf _ k2161_1)) (.split 2 (.leaf _ k2161_2) (.leaf _ k2161_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2162)
      (.split 3 (.split 2 (.leaf _ k2162_0) (.leaf _ k2162_1)) (.split 2 (.leaf _ k2162_2) (.leaf _ k2162_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2163)
      (.split 3 (.split 2 (.leaf _ k2163_0) (.leaf _ k2163_1)) (.split 2 (.leaf _ k2163_2) (.leaf _ k2163_3))))

end C4.Cert.Dir030

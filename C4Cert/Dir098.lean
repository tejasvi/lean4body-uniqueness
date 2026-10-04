module

public import C4Check

public section

/-! Cells `3308 ≤ n < 3316` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir098

theorem k3308_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3308) 3).1 2).1
      88599891791793309725039358039533078689553338308443729173861055878060542077439621353680815417712448860230707881946363399474893745).isSome = true := by
  decide +kernel

theorem k3308_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3308) 3).1 2).2
      75144451685051301106292978369122823638948676172828272451008540032488458623693298885546736089603255903286513).isSome = true := by
  decide +kernel

theorem k3308_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3308) 3).2 2).1 1).1
      13424882282448511463250259183992458031926188475151427028184038572).isSome = true := by
  decide +kernel

theorem k3308_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3308) 3).2 2).1 1).2
      53636760172110989653617848520128933634426875601701387891783458604).isSome = true := by
  decide +kernel

theorem k3308_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3308) 3).2 2).2
      299323003008485755260347864363712347418023482445227449842509498965574281929554457038944709611192196971197105).isSome = true := by
  decide +kernel

theorem k3309_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3309) 3).1 2).1 1).1
      53511173756319975912601907065981752430311956032116829671037189180).isSome = true := by
  decide +kernel

theorem k3309_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3309) 3).1 2).1 1).2
      13696009114431990900891950411484053625143529804688212584558449441852).isSome = true := by
  decide +kernel

theorem k3309_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3309) 3).1 2).2
      4772828368762783676195379792145321080400565400112216766919810593557441259520798374833651646816203119911337137).isSome = true := by
  decide +kernel

theorem k3309_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3309) 3).2 2).1 1).1
      15749026844313884061060345636575444447876760916212071037554500671455803438138197392444).isSome = true := by
  decide +kernel

theorem k3309_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3309) 3).2 2).1 1).2
      3936583378270358671838683465589350222321890142832388813211462620371268736293394805708).isSome = true := by
  decide +kernel

theorem k3309_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3309) 3).2 2).2
      4758580768459472397506142767149196115459286605543794143076545337895702801201153696719201506919554410426527985).isSome = true := by
  decide +kernel

theorem k3310_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3310) 2).1 3).1 1).1
      3406966922824288556123735008287155714743505404696368384327089437756).isSome = true := by
  decide +kernel

theorem k3310_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3310) 2).1 3).1 1).2
      3927691824956841146201365851631052645544674970397020405269304845641486068126118933452).isSome = true := by
  decide +kernel

theorem k3310_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3310) 2).1 3).2 1).1
      850154490991538584970609390934623739597453641677724785242665335868).isSome = true := by
  decide +kernel

theorem k3310_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3310) 2).1 3).2 1).2
      53126594294549617530392404303216152235437665015937268680392330956).isSome = true := by
  decide +kernel

theorem k3310_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3310) 2).2 3).1 1).1
      851913460047796388875143774371195061857512503359589652648601369660).isSome = true := by
  decide +kernel

theorem k3310_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3310) 2).2 3).1 1).2
      53237565263592031117799761266834565484538145849750864377260429004).isSome = true := by
  decide +kernel

theorem k3310_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3310) 2).2 3).2 1).1
      212584646555924019457496401782614729701484470840510288831991725116).isSome = true := by
  decide +kernel

theorem k3310_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3310) 2).2 3).2 1).2
      13284840001733377181490757124448716496154364265712387032283060940).isSome = true := by
  decide +kernel

theorem k3311_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3311) 2).1 3).1 1).1
      2944688663434125193775303331857100148253196500028).isSome = true := by
  decide +kernel

theorem k3311_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3311) 2).1 3).1 1).2
      848734446981936824487750218031598105331014899925567183408399868876).isSome = true := by
  decide +kernel

theorem k3311_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3311) 2).1 3).2 1).1
      735244842643960879344164955706207900346048789564).isSome = true := by
  decide +kernel

theorem k3311_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3311) 2).1 3).2 1).2
      847660091203595594324929502808549720850045486594275088452072465356).isSome = true := by
  decide +kernel

theorem k3311_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3311) 2).2 3).1 1).1
      46022274436812649005400083367021824501450255420).isSome = true := by
  decide +kernel

theorem k3311_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3311) 2).2 3).1 1).2
      13264512208499878297312210101240607267099019803324336847575292620).isSome = true := by
  decide +kernel

theorem k3311_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3311) 2).2 3).2 1).1
      52992287145461975101320650004462950497745386289659672333228336076).isSome = true := by
  decide +kernel

theorem k3311_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3311) 2).2 3).2 1).2
      847864417926974499488859920759009198673766671142227599744158360524).isSome = true := by
  decide +kernel

theorem k3312_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3312) 2).1 3).1 1).1
      734465478626222735949417517286487262573062470716).isSome = true := by
  decide +kernel

theorem k3312_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3312) 2).1 3).1 1).2
      734442112116661991871807924477040503882293591100).isSome = true := by
  decide +kernel

theorem k3312_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3312) 2).1 3).2
      22275685503841579362109534679122858377474743373503315171243309168372648648871039998301166020184690214834408867645615603708756540476).isSome = true := by
  decide +kernel

theorem k3312_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3312) 2).2 3).1
      89197703448995989202480476174002833573087538716755355764352685562157943679365924590973714638001540739438463195721032184296516041788).isSome = true := by
  decide +kernel

theorem k3312_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3312) 2).2 3).2
      75525297757717017157494863953378366111940596720148790636480503524997248105653899862229861247402788959713705020).isSome = true := by
  decide +kernel

theorem k3313_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3313) 2).1 3).1
      75420863604791299003615332567796233022181479289434192651067334292500793417298734229654168547717724212081507388).isSome = true := by
  decide +kernel

theorem k3313_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3313) 2).1 3).2
      75371684094648625516347514406828956992150751809604812262878683408687586939196909160853520844412559086589885500).isSome = true := by
  decide +kernel

theorem k3313_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3313) 2).2 3).1
      75429632695418103390375207470527494108905335595173085925862953515680008289162909553132645645863436756978449468).isSome = true := by
  decide +kernel

theorem k3313_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3313) 2).2 3).2
      1021649497143519776789674983953251148159563605759397799625890625442398257676982459560672316).isSome = true := by
  decide +kernel

theorem k3314_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3314) 2).1 3).1
      15952866036936451013083729239031106626734862733458029231285394080285786559356242955648060).isSome = true := by
  decide +kernel

theorem k3314_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3314) 2).1 3).2
      3986638641003048961997314097448976514667117040593251905585159969874756720528305917049916).isSome = true := by
  decide +kernel

theorem k3314_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3314) 2).2 3).1
      3988763494390419226532437437190325364266541034450439090200825685777831188120528985209916).isSome = true := by
  decide +kernel

theorem k3314_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3314) 2).2 3).2
      216125157822737963537807624930238318389277194690357778483702846405692).isSome = true := by
  decide +kernel

theorem k3315_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3315) 3).1 1).1
      54037214386896183890721327875019674269958085375129737772750175878204).isSome = true := by
  decide +kernel

theorem k3315_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3315) 3).1 1).2
      996866519112874798248188699228613010566022276038956834214978061721335977655010510453820).isSome = true := by
  decide +kernel

theorem k3315_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3315) 3).2 1).1
      249005806658183602246493839909155751028040191756205181104968342425355920990875518647356).isSome = true := by
  decide +kernel

theorem k3315_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3315) 3).2 1).2
      215978265908712991847503472986592109520313598938306154115662229486652).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3308 3316 :=
  (Cover.one (box := dirCellBox) (n := 3308)
      (.split 3 (.split 2 (.leaf _ k3308_0) (.leaf _ k3308_1)) (.split 2 (.split 1 (.leaf _ k3308_2) (.leaf _ k3308_3)) (.leaf _ k3308_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3309)
      (.split 3 (.split 2 (.split 1 (.leaf _ k3309_0) (.leaf _ k3309_1)) (.leaf _ k3309_2)) (.split 2 (.split 1 (.leaf _ k3309_3) (.leaf _ k3309_4)) (.leaf _ k3309_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3310)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3310_0) (.leaf _ k3310_1)) (.split 1 (.leaf _ k3310_2) (.leaf _ k3310_3))) (.split 3 (.split 1 (.leaf _ k3310_4) (.leaf _ k3310_5)) (.split 1 (.leaf _ k3310_6) (.leaf _ k3310_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3311)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3311_0) (.leaf _ k3311_1)) (.split 1 (.leaf _ k3311_2) (.leaf _ k3311_3))) (.split 3 (.split 1 (.leaf _ k3311_4) (.leaf _ k3311_5)) (.split 1 (.leaf _ k3311_6) (.leaf _ k3311_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3312)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3312_0) (.leaf _ k3312_1)) (.leaf _ k3312_2)) (.split 3 (.leaf _ k3312_3) (.leaf _ k3312_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3313)
      (.split 2 (.split 3 (.leaf _ k3313_0) (.leaf _ k3313_1)) (.split 3 (.leaf _ k3313_2) (.leaf _ k3313_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3314)
      (.split 2 (.split 3 (.leaf _ k3314_0) (.leaf _ k3314_1)) (.split 3 (.leaf _ k3314_2) (.leaf _ k3314_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3315)
      (.split 3 (.split 1 (.leaf _ k3315_0) (.leaf _ k3315_1)) (.split 1 (.leaf _ k3315_2) (.leaf _ k3315_3))))

end C4.Cert.Dir098

module

public import C4Check

public section

/-! Cells `2917 ≤ n < 2925` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir074

theorem k2917_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2917) 3).1 2).1 1).1
      214112495374237786079977381084279603335294714884455536204089521724).isSome = true := by
  decide +kernel

theorem k2917_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2917) 3).1 2).1 1).2
      53518375823313940628526219466872475990367832264352444252498031164).isSome = true := by
  decide +kernel

theorem k2917_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2917) 3).1 2).2 1).1
      246867564742548288342911579602642424714963330705217907936398513271595423353924058540).isSome = true := by
  decide +kernel

theorem k2917_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2917) 3).1 2).2 1).2
      13380690076333556988387251897921692874850372197101251850734763180).isSome = true := by
  decide +kernel

theorem k2917_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2917) 3).2 2).1 1).1
      3415681748004182386236518568790572092373012882829932767044662446652).isSome = true := by
  decide +kernel

theorem k2917_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2917) 3).2 2).1 1).2
      15750649033588376669782362044521823365509615622539376130839592649940804394106872511548).isSome = true := by
  decide +kernel

theorem k2917_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2917) 3).2 2).2
      1218835360656801627908042759985086318574177583708271695564779500343341700242682491626441169742139247106352204017).isSome = true := by
  decide +kernel

theorem k2918_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2918) 3).1 2).1 1).1
      1005798741719917932466999575341158439411851141730780870803499209687328985331152004313660).isSome = true := by
  decide +kernel

theorem k2918_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2918) 3).1 2).1 1).2
      15713906618765926794747777007463916572127271712348409860525227209007210011155576503356).isSome = true := by
  decide +kernel

theorem k2918_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2918) 3).1 2).2
      4864095363992388401218539046873928135589488915937558694705657948749760046692366023652863214013844861442317601009).isSome = true := by
  decide +kernel

theorem k2918_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2918) 3).2 2).1 1).1
      3400983592588026174328422055263130455495551246512192484136779103292).isSome = true := by
  decide +kernel

theorem k2918_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2918) 3).2 2).1 1).2
      3400640316725535534141829758498977704242355062325140151635920731196).isSome = true := by
  decide +kernel

theorem k2918_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2918) 3).2 2).2 1).1
      3401630769623920090040934784474976029783879534919019840685605764156).isSome = true := by
  decide +kernel

theorem k2918_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2918) 3).2 2).2 1).2
      850345866092458590492207694576536774215113504583645464432622746684).isSome = true := by
  decide +kernel

theorem k2919_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2919) 2).1 3).1 1).1
      3395678030842467919319440767218640809344626619446018853602559114300).isSome = true := by
  decide +kernel

theorem k2919_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2919) 2).1 3).1 1).2
      3395394558497476956800812908415973081901513371367045732127108545596).isSome = true := by
  decide +kernel

theorem k2919_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2919) 2).1 3).2 1).1
      3391129523659692375584764017896881519375859138598626132267076729916).isSome = true := by
  decide +kernel

theorem k2919_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2919) 2).1 3).2 1).2
      847777906518348095615446090567358920951057842051703634674117459004).isSome = true := by
  decide +kernel

theorem k2919_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2919) 2).2 3).1
      89463853464964181781259403431885243160730467212883033793369855351060684624178438791680110790583512792708483015019886170068853439548).isSome = true := by
  decide +kernel

theorem k2919_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2919) 2).2 3).2
      1210252347479564003528511716389385394157473108611655845243302380774011716654974444708485654863404640891292531772).isSome = true := by
  decide +kernel

theorem k2920_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2920) 2).1 3).1 1).1
      734488624973076978122939157407246628390452804668).isSome = true := by
  decide +kernel

theorem k2920_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2920) 2).1 3).1 1).2
      734470345344625912597243163320252889676974341180).isSome = true := by
  decide +kernel

theorem k2920_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2920) 2).1 3).2 1).1
      846104140487255389851589990125459927345585283292590665221026046924).isSome = true := by
  decide +kernel

theorem k2920_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2920) 2).1 3).2 1).2
      3384310474221963962677812756354654664115096389435817894136365071420).isSome = true := by
  decide +kernel

theorem k2920_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2920) 2).2 3).1
      1209482838378259115843262725778698923378724427410529181601647185186251943310432079464288486797182785309697162300).isSome = true := by
  decide +kernel

theorem k2920_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2920) 2).2 3).2
      75561456301829923584159503426113469860086985910377316758444095657864348862866843981706260578590396177984470076).isSome = true := by
  decide +kernel

theorem k2921_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2921) 3).1 2).1
      1206686835111109241558802409981457646135316872195712923118921475889232607286916624803342761749112533226743872572).isSome = true := by
  decide +kernel

theorem k2921_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2921) 3).1 2).2
      75430596170610399511763449781553330771724260535069179018312384087862184958303616961656462872917845248942750780).isSome = true := by
  decide +kernel

theorem k2921_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2921) 3).2 2).1
      18843069844200473111293157892528574082456087924088669905035444968657078232987567361014370407517158836509752380).isSome = true := by
  decide +kernel

theorem k2921_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2921) 3).2 2).2
      18845816969871821900278530850632617304607690698382517660780664370457378872815245090853092860816173239866375228).isSome = true := by
  decide +kernel

theorem k2922_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2922) 3).1 2).1
      294268436368399511560014787493463828525169786676440231860051408974183486744731317083559300001835037063003196).isSome = true := by
  decide +kernel

theorem k2922_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2922) 3).1 2).2
      63814389622849552144052868647471537441476802966344427922922933913159573951565257299868732).isSome = true := by
  decide +kernel

theorem k2922_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2922) 3).2 2).1
      249154218536850827280814292217849408495213929182730067413557644902495372601913215695932).isSome = true := by
  decide +kernel

theorem k2922_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2922) 3).2 2).2
      54053792940722859092434076587643504770227654063079655102340626267196).isSome = true := by
  decide +kernel

theorem k2923_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2923) 3).1 1).1
      54005008938080263082324333819209606059186957782721632083640772082748).isSome = true := by
  decide +kernel

theorem k2923_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2923) 3).1 1).2
      54032849440996238998408631816474965211584985347444958921920831175740).isSome = true := by
  decide +kernel

theorem k2923_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2923) 3).2 1).1
      843553162435244752679190404110947684872020709962730559922226799564).isSome = true := by
  decide +kernel

theorem k2923_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2923) 3).2 1).2
      13497596682722254303535411914044465507323498850333694232246556441660).isSome = true := by
  decide +kernel

theorem k2924_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2924) 3).1 1).1
      210829051441979583876145846994450113266964437709258255675954809548).isSome = true := by
  decide +kernel

theorem k2924_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2924) 3).1 1).2
      843381308336262176925111573487913637859563271646653093556925703116).isSome = true := by
  decide +kernel

theorem k2924_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2924) 3).2
      346866343290671780781679249542969763757259808233091012094531983113389107479410238953454785676417568197339546677171900301704551217).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2917 2925 :=
  (Cover.one (box := dirCellBox) (n := 2917)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2917_0) (.leaf _ k2917_1)) (.split 1 (.leaf _ k2917_2) (.leaf _ k2917_3))) (.split 2 (.split 1 (.leaf _ k2917_4) (.leaf _ k2917_5)) (.leaf _ k2917_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2918)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2918_0) (.leaf _ k2918_1)) (.leaf _ k2918_2)) (.split 2 (.split 1 (.leaf _ k2918_3) (.leaf _ k2918_4)) (.split 1 (.leaf _ k2918_5) (.leaf _ k2918_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2919)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2919_0) (.leaf _ k2919_1)) (.split 1 (.leaf _ k2919_2) (.leaf _ k2919_3))) (.split 3 (.leaf _ k2919_4) (.leaf _ k2919_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2920)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2920_0) (.leaf _ k2920_1)) (.split 1 (.leaf _ k2920_2) (.leaf _ k2920_3))) (.split 3 (.leaf _ k2920_4) (.leaf _ k2920_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2921)
      (.split 3 (.split 2 (.leaf _ k2921_0) (.leaf _ k2921_1)) (.split 2 (.leaf _ k2921_2) (.leaf _ k2921_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2922)
      (.split 3 (.split 2 (.leaf _ k2922_0) (.leaf _ k2922_1)) (.split 2 (.leaf _ k2922_2) (.leaf _ k2922_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2923)
      (.split 3 (.split 1 (.leaf _ k2923_0) (.leaf _ k2923_1)) (.split 1 (.leaf _ k2923_2) (.leaf _ k2923_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2924)
      (.split 3 (.split 1 (.leaf _ k2924_0) (.leaf _ k2924_1)) (.leaf _ k2924_2)))

end C4.Cert.Dir074

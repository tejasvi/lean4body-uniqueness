module

public import C4Check

public section

/-! Cells `3650 ≤ n < 3674` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir118

theorem k3650_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3650) 2).1 3).1
      18382884270402911493802679771981848381929324696313379896006776843330018901118488933228734467352033297287996).isSome = true := by
  decide +kernel

theorem k3650_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3650) 2).1 3).2
      1148558867348340758065201716893777207131664841634607979814640270111342721852514784126935864989903667284796).isSome = true := by
  decide +kernel

theorem k3650_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3650) 2).2 3).1
      4596269151196027712818428134323537437535165335405625947839667346609309815857257137786885525212492120185404).isSome = true := by
  decide +kernel

theorem k3650_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3650) 2).2 3).2
      3891973580305484225944850270596883700915672912041813562014892386907087173093766329916).isSome = true := by
  decide +kernel

theorem k3651_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3651) 2).1 3).1
      1148266289456107120617361605673857440788601924590612615922457719986232448661750247916388124251214653115196).isSome = true := by
  decide +kernel

theorem k3651_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3651) 2).1 3).2
      13178620332817442146057606885825032784965416027301181746782358332).isSome = true := by
  decide +kernel

theorem k3651_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3651) 2).2 1).1
      15561407026001792931522330848955019537314284259915114325315366873035602776876155620924).isSome = true := by
  decide +kernel

theorem k3651_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3651) 2).2 1).2
      15561255121253805051102782883448109809025506553064301781634636311318469933914736511804).isSome = true := by
  decide +kernel

theorem k3652_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3652) 2).1
      338724225101701302509555586923239764372597786197844822769333822579652036293684393760926097019581166676517772663835470708700403).isSome = true := by
  decide +kernel

theorem k3652_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3652) 2).2
      1354979170535503667170508595606100802026638879963246813358078620626370876927448086101083011040734166451557148114019309440063731).isSome = true := by
  decide +kernel

theorem k3653_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3653) 2).1
      15186055903550774327619243935914516550646909494274768035662556279905723571936348529).isSome = true := by
  decide +kernel

theorem k3653_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3653) 2).2
      338670589987746759436300445064380586327475958177042302709994139582430157570687018010163905061433723925926693949851757532509425).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 3654 3656 [
    21162507045158392087310070978717921460966219808927744687785077170299244690062622947061582461783192612903035738549502515981382,
    11420689537944808610918175094753907342595653718] = true := by
  decide +kernel

theorem c5 : allCells dirCell 3656 3671 [
    696965485671942407315485225002900045817282, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    878889366351590085299516428612491963329968804017048300098414731379] = true := by
  decide +kernel

theorem k3671_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3671) 3).1 2).1
      6447509692773227071184120397241278044969175917971678318262066591638432765653762152838101302614353165037135246689133303703054812725693942536203847).isSome = true := by
  decide +kernel

theorem k3671_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3671) 3).1 2).2
      18534141007024489658608068172443384267277851290340781229209523135452683516491723144205881534903757003123).isSome = true := by
  decide +kernel

theorem k3671_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3671) 3).2 2).1 3).1
      64081424748131547638448708370111264024701477548998704711046055613841738528882266365106).isSome = true := by
  decide +kernel

theorem k3671_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3671) 3).2 2).1 3).2
      15952995441775256856861573375688544205640020822734908333117313338000892247952616545457).isSome = true := by
  decide +kernel

theorem k3671_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3671) 3).2 2).2
      309050989201205830743231511985988328185988551293758479021957477604477366904067161186109658927604806740889590985).isSome = true := by
  decide +kernel

theorem k3672_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3672) 3).1 2).1 2).1
      75088343953492558201344284495772513485025666825581715842399963679686069888524644735650168951630188245261105).isSome = true := by
  decide +kernel

theorem k3672_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3672) 3).1 2).1 2).2
      254172623947406380872645733107879531979210844635372903533674531171839586867744079058739).isSome = true := by
  decide +kernel

theorem k3672_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3672) 3).1 2).2 1).1
      3977514126844704084664892380070458257456907972577884945120485886643293960996650096434).isSome = true := by
  decide +kernel

theorem k3672_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3672) 3).1 2).2 1).2
      3972381011060260782896099281511782451370903553399569037234452023895804241534337062706).isSome = true := by
  decide +kernel

theorem k3672_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3672) 3).2 2).1 1).1
      1013524526548984098414259290576599176357987293965265949004069988464167521190835912809266).isSome = true := by
  decide +kernel

theorem k3672_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3672) 3).2 2).1 1).2
      1194942451993826567007120522064060801415771839980733045087346519135636047505881551239717715010311390462597939).isSome = true := by
  decide +kernel

theorem k3672_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3672) 3).2 2).2 1).1
      253189612911177312668554304993758164845036767330853514783513151373129245095743947895756).isSome = true := by
  decide +kernel

theorem k3672_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3672) 3).2 2).2 1).2
      63293480018108884389154558619782937704383325263821005644377088468819353528807687273164).isSome = true := by
  decide +kernel

theorem k3673_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3673) 2).1 3).1 1).1
      16143713039237400991518806800073863376069817325581364728755341458593233402119291622805299).isSome = true := by
  decide +kernel

theorem k3673_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3673) 2).1 3).1 1).2
      64611931385074153520817133639603433453994410449103228969100224786509556035493935569144626).isSome = true := by
  decide +kernel

theorem k3673_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3673) 2).1 3).2 1).1
      350856762457083416381317216703689390832146428692417476844006869086869889798317114512604177870702390589694449399813859410532053964).isSome = true := by
  decide +kernel

theorem k3673_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3673) 2).1 3).2 1).2
      1030874212001687271375938016912027972318793023418042693119089589682716199058874539918109490).isSome = true := by
  decide +kernel

theorem k3673_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3673) 2).2 3).1 1).1
      252541043008343590746997025627007657180137251422450397692020529083749183624323385380556).isSome = true := by
  decide +kernel

theorem k3673_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3673) 2).2 3).1 1).2
      64634800637678868563762066328772565056404164730973362758955504688051130721685897634761522).isSome = true := by
  decide +kernel

theorem k3673_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3673) 2).2 3).2 1).1
      13651058148635241620391666002560128588866115059997228714850243623628).isSome = true := by
  decide +kernel

theorem k3673_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3673) 2).2 3).2 1).2
      64454231496840008431326171623960627675626723182021901017757859585451379271983020165794610).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3650 3674 :=
  (Cover.one (box := dirCellBox) (n := 3650)
      (.split 2 (.split 3 (.leaf _ k3650_0) (.leaf _ k3650_1)) (.split 3 (.leaf _ k3650_2) (.leaf _ k3650_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3651)
      (.split 2 (.split 3 (.leaf _ k3651_0) (.leaf _ k3651_1)) (.split 1 (.leaf _ k3651_2) (.leaf _ k3651_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3652)
      (.split 2 (.leaf _ k3652_0) (.leaf _ k3652_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3653)
      (.split 2 (.leaf _ k3653_0) (.leaf _ k3653_1))).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 3671)
      (.split 3 (.split 2 (.leaf _ k3671_0) (.leaf _ k3671_1)) (.split 2 (.split 3 (.leaf _ k3671_2) (.leaf _ k3671_3)) (.leaf _ k3671_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3672)
      (.split 3 (.split 2 (.split 2 (.leaf _ k3672_0) (.leaf _ k3672_1)) (.split 1 (.leaf _ k3672_2) (.leaf _ k3672_3))) (.split 2 (.split 1 (.leaf _ k3672_4) (.leaf _ k3672_5)) (.split 1 (.leaf _ k3672_6) (.leaf _ k3672_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3673)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3673_0) (.leaf _ k3673_1)) (.split 1 (.leaf _ k3673_2) (.leaf _ k3673_3))) (.split 3 (.split 1 (.leaf _ k3673_4) (.leaf _ k3673_5)) (.split 1 (.leaf _ k3673_6) (.leaf _ k3673_7)))))

end C4.Cert.Dir118

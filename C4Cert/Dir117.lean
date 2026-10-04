module

public import C4Check

public section

/-! Cells `3645 ≤ n < 3650` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir117

theorem k3645_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).1 3).1 2).1 1).1
      53435181372689488769966679700498225618889082680326715119566219980).isSome = true := by
  decide +kernel

theorem k3645_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).1 3).1 2).1 1).2
      13354812865400510800345441563838737405530526139356470039035747020).isSome = true := by
  decide +kernel

theorem k3645_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).1 3).1 2).2 1).1
      13351186508947521359604770399560280031588770824237888806789290700).isSome = true := by
  decide +kernel

theorem k3645_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).1 3).1 2).2 1).2
      13347133487340942654760313882378095781196932589701900151442348748).isSome = true := by
  decide +kernel

theorem k3645_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3645) 2).1 3).2 2).1
      1401234082510613429484210423658770703240287316942458570517400758840491032548620429261357499931550297858668608688799081390055739185).isSome = true := by
  decide +kernel

theorem k3645_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).1 3).2 2).2 1).1
      13325398489266388170990067108122428781222613180451338853092399820).isSome = true := by
  decide +kernel

theorem k3645_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).1 3).2 2).2 1).2
      13309274294526660520582925628743928232008298882544011376823081676).isSome = true := by
  decide +kernel

theorem k3645_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).2 3).1 2).1 1).1
      13355667409441664969132585734316634674521656906066382984989612748).isSome = true := by
  decide +kernel

theorem k3645_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).2 3).1 2).1 1).2
      13351840663866516396279098626166009557928317065142148475836144332).isSome = true := by
  decide +kernel

theorem k3645_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).2 3).1 2).2 1).1
      13359447640714349782659145356105748679646861584340045939665771212).isSome = true := by
  decide +kernel

theorem k3645_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).2 3).1 2).2 1).2
      46335529408854006700605894614852529003142040268).isSome = true := by
  decide +kernel

theorem k3645_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).2 3).2 1).1 2).1
      13316879125880866548568147706875089754384684465743664079254821580).isSome = true := by
  decide +kernel

theorem k3645_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3645) 2).2 3).2 1).1 2).2
      13320953982486244628118602949274549317153320044775940554627717836).isSome = true := by
  decide +kernel

theorem k3645_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3645) 2).2 3).2 1).2
      350645478737223020937654958776948257027766846603164721615505744408324740353583408640887117194505491936732336561914015869057264434).isSome = true := by
  decide +kernel

theorem k3646_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3646) 2).1 3).1 1).1 2).1
      849828095823877195925012595525006595462745543744987646044216802364).isSome = true := by
  decide +kernel

theorem k3646_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3646) 2).1 3).1 1).1 2).2
      53136007862910241912193425619008317464530060841723398858475957308).isSome = true := by
  decide +kernel

theorem k3646_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3646) 2).1 3).1 1).2
      75820388256991350897010924162784605804799683391047272710818587160480294960370556088433575757262196326802845938).isSome = true := by
  decide +kernel

theorem k3646_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3646) 2).1 3).2 1).1
      1051469606637045135100666677137360085367682975926880995501023392685401308771776544388265996530).isSome = true := by
  decide +kernel

theorem k3646_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3646) 2).1 3).2 1).2
      1396329565608485384533559057558078343462220092770885246509717332162411924307527183612893265634043950194425791551585732644483494130).isSome = true := by
  decide +kernel

theorem k3646_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3646) 2).2 3).1 1).1
      16066745781842141077243668387360082267315204692984864418809591417446182690974225700121394).isSome = true := by
  decide +kernel

theorem k3646_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3646) 2).2 3).1 1).2
      4016063611854912591784445919599559637811225406241170681975275284234519618975852539570994).isSome = true := by
  decide +kernel

theorem k3646_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3646) 2).2 3).2 1).1
      4733312812552193310675609350833007329698835547709245144262954002749203701399002474478866149022152411209055292).isSome = true := by
  decide +kernel

theorem k3646_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3646) 2).2 3).2 1).2
      256564273070611273186669950561456389428004253250606290135662395898940217706851390710804722).isSome = true := by
  decide +kernel

theorem k3647_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3647) 2).1 3).1 1).1
      16007487414562283144769375487563634677646265696226728836130984343363789171820587789316668).isSome = true := by
  decide +kernel

theorem k3647_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3647) 2).1 3).1 1).2
      18471218381670895702825562837334378605756673551291639940245757680934030570333028885235764295330019461820988).isSome = true := by
  decide +kernel

theorem k3647_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3647) 2).1 3).2 1).1
      3997504218645540977805710095881272036710165515793165664030343078248256175887939369159228).isSome = true := by
  decide +kernel

theorem k3647_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3647) 2).1 3).2 1).2
      18433337881915374534899803453406706962413665175791743015149276802547737505007951896115270977983814209358396).isSome = true := by
  decide +kernel

theorem k3647_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3647) 2).2 3).1 1).1
      62556621628860720928326501467796321608222634284307320977012246429491673736209867062332).isSome = true := by
  decide +kernel

theorem k3647_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3647) 2).2 3).1 1).2
      62547973233510405636981038341598718089598735217009139018660729908308983620407075388476).isSome = true := by
  decide +kernel

theorem k3647_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3647) 2).2 3).2 1).1
      15620869209289778719216369494127779419993768481491578305341356096740291082400888110140).isSome = true := by
  decide +kernel

theorem k3647_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3647) 2).2 3).2 1).2
      15619322075001148831577568305278308758751436017923924394526190465683014745695394315324).isSome = true := by
  decide +kernel

theorem k3648_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3648) 2).1 3).1 1).1
      15602937841741056679804999817250858530859474418337424124512862584540313363149579875900).isSome = true := by
  decide +kernel

theorem k3648_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3648) 2).1 3).1 1).2
      211440248228000281492676184973904067954473081837970325712685889084).isSome = true := by
  decide +kernel

theorem k3648_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3648) 2).1 3).2 1).1
      52828003721474013687676099166434212582968933769808328376390645308).isSome = true := by
  decide +kernel

theorem k3648_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3648) 2).1 3).2 1).2
      52823750862452358835716020102649150842363363479427345159377253948).isSome = true := by
  decide +kernel

theorem k3648_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3648) 2).2 3).1 1).1
      998868605093984458944995128254824670913503255174173867610134927733306178062464379777596).isSome = true := by
  decide +kernel

theorem k3648_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3648) 2).2 3).1 1).2
      15605948703837995464875165454758453001904124444925644333732764686240927988121668678204).isSome = true := by
  decide +kernel

theorem k3648_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3648) 2).2 3).2 1).1
      845417814344734572655621258781360928644927054997267153194405327420).isSome = true := by
  decide +kernel

theorem k3648_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3648) 2).2 3).2 1).2
      45826090316568643998473600333016360478368582204).isSome = true := by
  decide +kernel

theorem k3649_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3649) 2).1 3).1
      25642714239035157177798512856447072217500775693329310229476164397002297722505573480350546779497912419859179292346236237387966333861132148950976351036).isSome = true := by
  decide +kernel

theorem k3649_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3649) 2).1 3).2
      347347353823005376426391394781263352278436520934500421156456867574020815323563192346809657384022316165104373668456844413231421681).isSome = true := by
  decide +kernel

theorem k3649_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3649) 2).2 3).1
      1205905604305032940274702260437201471583942323281888081709208914346029640632717887030842048112880391481344903409).isSome = true := by
  decide +kernel

theorem k3649_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3649) 2).2 3).2
      5428481909161427829642138448091119179486746129808194940454353443677953382054942262710298773966062771689717111370403941892217404).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3645 3650 :=
  (Cover.one (box := dirCellBox) (n := 3645)
      (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3645_0) (.leaf _ k3645_1)) (.split 1 (.leaf _ k3645_2) (.leaf _ k3645_3))) (.split 2 (.leaf _ k3645_4) (.split 1 (.leaf _ k3645_5) (.leaf _ k3645_6)))) (.split 3 (.split 2 (.split 1 (.leaf _ k3645_7) (.leaf _ k3645_8)) (.split 1 (.leaf _ k3645_9) (.leaf _ k3645_10))) (.split 1 (.split 2 (.leaf _ k3645_11) (.leaf _ k3645_12)) (.leaf _ k3645_13))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3646)
      (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k3646_0) (.leaf _ k3646_1)) (.leaf _ k3646_2)) (.split 1 (.leaf _ k3646_3) (.leaf _ k3646_4))) (.split 3 (.split 1 (.leaf _ k3646_5) (.leaf _ k3646_6)) (.split 1 (.leaf _ k3646_7) (.leaf _ k3646_8))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3647)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3647_0) (.leaf _ k3647_1)) (.split 1 (.leaf _ k3647_2) (.leaf _ k3647_3))) (.split 3 (.split 1 (.leaf _ k3647_4) (.leaf _ k3647_5)) (.split 1 (.leaf _ k3647_6) (.leaf _ k3647_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3648)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3648_0) (.leaf _ k3648_1)) (.split 1 (.leaf _ k3648_2) (.leaf _ k3648_3))) (.split 3 (.split 1 (.leaf _ k3648_4) (.leaf _ k3648_5)) (.split 1 (.leaf _ k3648_6) (.leaf _ k3648_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3649)
      (.split 2 (.split 3 (.leaf _ k3649_0) (.leaf _ k3649_1)) (.split 3 (.leaf _ k3649_2) (.leaf _ k3649_3))))

end C4.Cert.Dir117

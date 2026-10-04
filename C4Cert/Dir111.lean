module

public import C4Check

public section

/-! Cells `3587 ≤ n < 3588` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir111

theorem k3587_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).1 3).1 1).1
      1029174208596340544397688518858174516367561948196715574963996162662222015500665497426737).isSome = true := by
  decide +kernel

theorem k3587_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).1 3).1 1).2
      64303481871841847290477192330637030303535234648380014071327484835879168976026900060978).isSome = true := by
  decide +kernel

theorem k3587_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).1 3).2 1).1
      63997672358775666491707935780105121901296211020643162976459376319084786069267755224012).isSome = true := by
  decide +kernel

theorem k3587_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).1 3).2 1).2
      63966511520719889698732865349051985219206575197375907179284507513742269167778288786226).isSome = true := by
  decide +kernel

theorem k3587_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).2 3).1 1).1
      1005649835899584440677848349656299414815579940495793460986649085260467144340002463436).isSome = true := by
  decide +kernel

theorem k3587_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).2 3).1 1).2
      64323375415965968951215665931138951556891778102159174685078061682324322541408767729202).isSome = true := by
  decide +kernel

theorem k3587_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).2 3).2 1).1
      1001262199988473774726548064638282187142775958775676091275995433854599209313095278284).isSome = true := by
  decide +kernel

theorem k3587_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).2 3).2 1).2
      1000492674711207008024272247914818118269671610469313422552698712439818535289602596556).isSome = true := by
  decide +kernel

theorem k3587_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).2 2).1 3).1 1).1
      63713724565890062677318593449458793362980177892123388381779847860834266108355667241932).isSome = true := by
  decide +kernel

theorem k3587_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).2 2).1 3).1 1).2
      3984583479941099138647317441700876116146453547248500814738900464802100620589599151922).isSome = true := by
  decide +kernel

theorem k3587_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).2 2).1 3).2 1).1
      3967807297703128327797761270387830855427019209166404693283202927774519662479704289068).isSome = true := by
  decide +kernel

theorem k3587_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).2 2).1 3).2 1).2
      13435223096442981978196925378619646132313417469696225407695154988).isSome = true := by
  decide +kernel

theorem k3587_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).2 2).2 3).1 1).1
      3987079186646396546767154682677433424568366086634350521201889113279858353203154875340).isSome = true := by
  decide +kernel

theorem k3587_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).2 2).2 3).1 1).2
      996124352106731328623090796601197871277513643882254245669058782450997958594099306188).isSome = true := by
  decide +kernel

theorem k3587_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).2 2).2 3).2
      76781594275820888037521185575530183186022731095505836994957695477966103076968814147279003907487640436693396273).isSome = true := by
  decide +kernel

theorem k3587_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).1 2).1 3).1
      4863826292967717626605100239062651344205427926022004615970013840431992029916718050625408696065612840845135665).isSome = true := by
  decide +kernel

theorem k3587_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).1 2).1 3).2
      89339123882676852810533327176871283923463200183211178927500376357977851725832255392392261888312420290588175163762935163755850545).isSome = true := by
  decide +kernel

theorem k3587_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).1 2).2 3).1
      76132443226861398578225898387885333652769640116292676138144483208030230867993351324883278937224777010092849).isSome = true := by
  decide +kernel

theorem k3587_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).1 2).2 3).2
      75742081274916333156252951255157626759076764230832078654796706941240042267442381441566222005979222753516337).isSome = true := by
  decide +kernel

theorem k3587_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).2 2).1 3).1
      77148099561265634216288674261915939194559164356064956391534778330632917093577076546753831041367432159364541233).isSome = true := by
  decide +kernel

theorem k3587_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).2 2).1 3).2
      1202120661098287553073824390266648938259714128152078154074363706428489402741387176784084152150573806673034033).isSome = true := by
  decide +kernel

theorem k3587_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).2 2).2 3).1
      1206573995439715102746327083012957218649031586494323875535460370972402734031316853327504911780261837247470385).isSome = true := by
  decide +kernel

theorem k3587_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).2 2).2 3).2
      4072814228158545344013878524824180022255746035645443834766152348944393516476769996532529).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3587 3588 :=
  (Cover.one (box := dirCellBox) (n := 3587)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3587_0) (.leaf _ k3587_1)) (.split 1 (.leaf _ k3587_2) (.leaf _ k3587_3))) (.split 3 (.split 1 (.leaf _ k3587_4) (.leaf _ k3587_5)) (.split 1 (.leaf _ k3587_6) (.leaf _ k3587_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3587_8) (.leaf _ k3587_9)) (.split 1 (.leaf _ k3587_10) (.leaf _ k3587_11))) (.split 3 (.split 1 (.leaf _ k3587_12) (.leaf _ k3587_13)) (.leaf _ k3587_14)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3587_15) (.leaf _ k3587_16)) (.split 3 (.leaf _ k3587_17) (.leaf _ k3587_18))) (.split 2 (.split 3 (.leaf _ k3587_19) (.leaf _ k3587_20)) (.split 3 (.leaf _ k3587_21) (.leaf _ k3587_22))))))

end C4.Cert.Dir111

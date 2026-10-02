module

public import C4Check

public section

/-! Cells `2356 ≤ n < 2358` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir038

theorem k2356_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).1 2).1 3).1
      15725068331787499687378399033067586617591716560087561875855590683951109611321241622321).isSome = true := by
  decide +kernel

theorem k2356_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).1 2).1 3).2
      245490614967117823991453949690805861110153484075689942752622627587817990313572734769).isSome = true := by
  decide +kernel

theorem k2356_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).1 2).2 3).1
      3934313321342404525839195935479951737817896884358124323442892419897338834881837831985).isSome = true := by
  decide +kernel

theorem k2356_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).1 2).2 3).2
      3928098061540673624556438330999747970889507567442240815022301383386604544417610962737).isSome = true := by
  decide +kernel

theorem k2356_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).2 2).1
      1858758487144625542384971848869239288177762076854389409943176945053964413491485505578528972080139670340652160530549965978354538938465032284113416157994966840244213191).isSome = true := by
  decide +kernel

theorem k2356_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2356) 2).1 3).2 2).2
      349733292022736844087797503424826227856570039694956280523416562915040840739424964494508371463847394947940975290339237658492427463).isSome = true := by
  decide +kernel

theorem k2356_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).1 2).1
      3938452034577030199806190349346618582814435115164517092512868407107530337212327270193).isSome = true := by
  decide +kernel

theorem k2356_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).1 2).2
      15771148770830153924389667005610927296517295403719768771214250713639356827525641755825).isSome = true := by
  decide +kernel

theorem k2356_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).2 2).1
      3931216498110215529688894262892267808901432053491166727435872066373197775259487475505).isSome = true := by
  decide +kernel

theorem k2356_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).1 3).2 2).2
      3935087494604561288865375232575503943297839302786369448266289258899863339985561474865).isSome = true := by
  decide +kernel

theorem k2356_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).2 2).1
      103200630379245770011941032176189633034003592371214144655918109309376550089274604293029332059010425240554085936822963212247640911194745194503342518515).isSome = true := by
  decide +kernel

theorem k2356_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).2 2).2 3).1
      982661553710170201287578305133955046715130649421037372693405758090205535067218738236).isSome = true := by
  decide +kernel

theorem k2356_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2356) 2).2 3).2 2).2 3).2
      981204904605937215075988252888257269625865281724052299766143694797203873080010439740).isSome = true := by
  decide +kernel

theorem k2357_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).1 2).1 3).1
      72195449329092319073267698124592005907967252201549595155888316008436769684509298108118403733122380076485).isSome = true := by
  decide +kernel

theorem k2357_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).1 2).1 3).2
      15271619366538431972863746091742181529129028360860241799283908473949535679451009393).isSome = true := by
  decide +kernel

theorem k2357_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).1 2).2 3).1
      341016262177796277484011104920698559506935500829102807107149563248489370243996730711452278718549236419493798024084772686755057).isSome = true := by
  decide +kernel

theorem k2357_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).1 2).2 3).2
      15271816087335441072334813321581109595364086428170007065238503139719505396269271409).isSome = true := by
  decide +kernel

theorem k2357_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).1 2).1
      73972351251529698532254248124216746329381133971436638323163436599501056663256017050877411236538620616692941).isSome = true := by
  decide +kernel

theorem k2357_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).1 2).2
      4731772867694465651168110600897344457695728056008039460166732557989412297010770898912091659481219797190663373).isSome = true := by
  decide +kernel

theorem k2357_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).2 2).1
      21280342054205053628947789480188147419265433879400711220702437891773130899483133154240736714712962362061810531428301354065329).isSome = true := by
  decide +kernel

theorem k2357_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2357) 2).2 3).2 2).2
      64037328307489389702597184958338534478828583847865372326127965778490688437601860801610957).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2356 2358 :=
  (Cover.one (box := dirCellBox) (n := 2356)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k2356_0) (.leaf _ k2356_1)) (.split 3 (.leaf _ k2356_2) (.leaf _ k2356_3))) (.split 2 (.leaf _ k2356_4) (.leaf _ k2356_5))) (.split 3 (.split 3 (.split 2 (.leaf _ k2356_6) (.leaf _ k2356_7)) (.split 2 (.leaf _ k2356_8) (.leaf _ k2356_9))) (.split 2 (.leaf _ k2356_10) (.split 3 (.leaf _ k2356_11) (.leaf _ k2356_12)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2357)
      (.split 2 (.split 2 (.split 3 (.leaf _ k2357_0) (.leaf _ k2357_1)) (.split 3 (.leaf _ k2357_2) (.leaf _ k2357_3))) (.split 3 (.split 2 (.leaf _ k2357_4) (.leaf _ k2357_5)) (.split 2 (.leaf _ k2357_6) (.leaf _ k2357_7)))))

end C4.Cert.Dir038

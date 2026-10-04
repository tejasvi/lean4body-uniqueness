module

public import C4Check

public section

/-! Cells `2444 ≤ n < 2469` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir046

theorem k2444_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2444) 3).1 2).1 1).1
      3902959494077170161558167609323501812156483721312467525635797381324083357271780219596).isSome = true := by
  decide +kernel

theorem k2444_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2444) 3).1 2).1 1).2
      62441993307889500822158530921886057915173312794292342872353415563133564799323954032332).isSome = true := by
  decide +kernel

theorem k2444_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2444) 3).1 2).2 1).1
      846485052280853747737813624345746806410168276732028972083743501004).isSome = true := by
  decide +kernel

theorem k2444_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2444) 3).1 2).2 1).2
      15600573056074338183783785640575870446044075900497753525925402604364187336087560998604).isSome = true := by
  decide +kernel

theorem k2444_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2444) 3).2 2).1 1).1
      974118620532558455116405209558601642935778887247727652832309141497368279088195164876).isSome = true := by
  decide +kernel

theorem k2444_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2444) 3).2 2).1 1).2
      52804115769377875726468896584602949279276404531935257692592746188).isSome = true := by
  decide +kernel

theorem k2444_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2444) 3).2 2).2 1).1
      3897520660040881207809853609010468336879346090277050952464930094099250464407755938508).isSome = true := by
  decide +kernel

theorem k2444_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2444) 3).2 2).2 1).2
      3897397855293499450795505443875655089785756599454665949048872555275598687153707014860).isSome = true := by
  decide +kernel

theorem k2445_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2445) 3).1 2).1
      21711434413824495489900667840676644986437340826350819319769594205090245631912410305892513521356524487112721195394337278483880753).isSome = true := by
  decide +kernel

theorem k2445_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2445) 3).1 2).2
      1603957935503940125202631972484088784553750098842115344180981934507727830404871644019706659362689227918785203156624760287870459356369208343818394417).isSome = true := by
  decide +kernel

theorem k2445_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2445) 3).2 2).1
      5425611995627623063146409736907408013607864679725023726061419226090023877141981387415034080245429439666828660658156783994788657).isSome = true := by
  decide +kernel

theorem k2445_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2445) 3).2 2).2
      5426502395232590208069598501360521915297565900512336205060129083458223518245057363544746543080450166782155180493305801210190641).isSome = true := by
  decide +kernel

theorem k2446_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2446) 2).1 3).1
      15565550696546790995596594958674568645490727169988537785293884323213886245935595674417).isSome = true := by
  decide +kernel

theorem k2446_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2446) 2).1 3).2
      3890189774215512158627651834030247244266314127120366072171668532439204379687749474097).isSome = true := by
  decide +kernel

theorem k2446_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2446) 2).2 3).1
      21698039597810654926621280622620287632575134344620733356017698771396912146964553947193982520801945098226090891793694479084371004).isSome = true := by
  decide +kernel

theorem k2446_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2446) 2).2 3).2
      18372397582226911362948845348860691472422059760631582438231812406345192445802557452270852169490733847665457).isSome = true := by
  decide +kernel

theorem k2447_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2447) 2).1
      25592179672042209042247488899373433475982593092708950627255177199474321694632382524488872877002528367233496942335640434839274793098989728745196977331).isSome = true := by
  decide +kernel

theorem k2447_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2447) 2).2
      5549826286245964527704959214728544119991073109653217236049377517004501213177130209629407311680657810702501515950943587556832623411).isSome = true := by
  decide +kernel

theorem k2448_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2448) 2).1
      18356447286998533219229504786431315930134544059433303545323116546420466190143962273236815418655366739588295).isSome = true := by
  decide +kernel

theorem k2448_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2448) 2).2
      6396213345088786105146947058421421572066377837252254521034170150693056312881179980537117871560145789080682715984201015547082159008968400781266345779).isSome = true := by
  decide +kernel

theorem k2449_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2449) 2).1
      15544246442952546491123939448840281337080604584591281921510740541106136882649985389261).isSome = true := by
  decide +kernel

theorem k2449_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2449) 2).2
      15544184609984823781891902698539218067146377669024174097926638629808526406929071707955).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 2450 2466 [
    24974368422812496307806793789179444676871369783814921607487960085572320638517246746747788681097552618508634830981885221325432110361470512056812998,
    37771842396589209179142, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2466 2467 [
    100045291120306083792931483493204345340966494323] = true := by
  decide +kernel

theorem k2467_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2467) 3).1 3).1
      22076759094245602695591345761855139529563513997804677822137061763772698628085930694762636685434730320946209861654143606953414).isSome = true := by
  decide +kernel

theorem k2467_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2467) 3).1 3).2 1).1
      18611619497919538154149869448108106502743825321621976942179095845226355849503496867744929026652667760710).isSome = true := by
  decide +kernel

theorem k2467_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2467) 3).1 3).2 1).2
      1372562941999416684630119090813044780101144833558042193240060065052485602038969576742058520619620606168251887094591044548082).isSome = true := by
  decide +kernel

theorem k2467_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2467) 3).2 3).1 1).1
      1365753527305778000272455893609469959494633111118095437848124336506414559696740154809564113881760412727345376726340306302450).isSome = true := by
  decide +kernel

theorem k2467_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2467) 3).2 3).1 1).2
      1398078830583747036929820570227374151438540649924407920532906069006651978939333941032773985046637823221570781217159438261507058).isSome = true := by
  decide +kernel

theorem k2467_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2467) 3).2 3).2 1).1
      1394438920533304033698664201900728207028502555034747176581929176640808622813480369925318423419200030087185374545852476657137138).isSome = true := by
  decide +kernel

theorem k2467_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2467) 3).2 3).2 1).2
      411459433959076522597937404041597100186361612695186341663294610248714008736046371571336092544068851850890786848944390729399459881941889268566053874).isSome = true := by
  decide +kernel

theorem k2468_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2468) 3).1 3).1 2).1 1).1
      3377361147373575831890037870724142134481087369112564292663801276).isSome = true := by
  decide +kernel

theorem k2468_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2468) 3).1 3).1 2).1 1).2
      54021199453419593858811899773545581462471003961918585286842479292).isSome = true := by
  decide +kernel

theorem k2468_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2468) 3).1 3).1 2).2
      86848444006581026491421396735179282338624168701513147964296244304211721926200560724156252712175074838828556445805872513246705).isSome = true := by
  decide +kernel

theorem k2468_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2468) 3).1 3).2 2).1 1).1
      215505619346374581754108892816521749455249870464574141129832684732).isSome = true := by
  decide +kernel

theorem k2468_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2468) 3).1 3).2 2).1 1).2
      3366753380280603777390855943349941202298257195443385230410815292).isSome = true := by
  decide +kernel

theorem k2468_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2468) 3).1 3).2 2).2
      1385575250108821202102238583136415061985246457235062764474748286535963123665854329107821530109309646813010005286869166917838321).isSome = true := by
  decide +kernel

theorem k2468_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2468) 3).2 2).1 3).1
      4907546067069423820969861970653186908208499247290517633203030500598612305024338637800863802897313856023829568753).isSome = true := by
  decide +kernel

theorem k2468_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2468) 3).2 2).1 3).2 1).1
      53617046468184178900730621334904465146173789906166702353831334716).isSome = true := by
  decide +kernel

theorem k2468_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2468) 3).2 2).1 3).2 1).2
      53609871569249031198791559406886355748381072477628624565035768380).isSome = true := by
  decide +kernel

theorem k2468_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2468) 3).2 2).2 1).1
      353120325257684793724069929107395516471147866806700823099430319690012962751160615741361078326112815967014444563880572093978211059).isSome = true := by
  decide +kernel

theorem k2468_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2468) 3).2 2).2 1).2
      19137630197697964043939795977338077925726420768185197738382358515481733138386812663128680511305556890064936179).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2444 2469 :=
  (Cover.one (box := dirCellBox) (n := 2444)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2444_0) (.leaf _ k2444_1)) (.split 1 (.leaf _ k2444_2) (.leaf _ k2444_3))) (.split 2 (.split 1 (.leaf _ k2444_4) (.leaf _ k2444_5)) (.split 1 (.leaf _ k2444_6) (.leaf _ k2444_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2445)
      (.split 3 (.split 2 (.leaf _ k2445_0) (.leaf _ k2445_1)) (.split 2 (.leaf _ k2445_2) (.leaf _ k2445_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2446)
      (.split 2 (.split 3 (.leaf _ k2446_0) (.leaf _ k2446_1)) (.split 3 (.leaf _ k2446_2) (.leaf _ k2446_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2447)
      (.split 2 (.leaf _ k2447_0) (.leaf _ k2447_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2448)
      (.split 2 (.leaf _ k2448_0) (.leaf _ k2448_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2449)
      (.split 2 (.leaf _ k2449_0) (.leaf _ k2449_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 2467)
      (.split 3 (.split 3 (.leaf _ k2467_0) (.split 1 (.leaf _ k2467_1) (.leaf _ k2467_2))) (.split 3 (.split 1 (.leaf _ k2467_3) (.leaf _ k2467_4)) (.split 1 (.leaf _ k2467_5) (.leaf _ k2467_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2468)
      (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k2468_0) (.leaf _ k2468_1)) (.leaf _ k2468_2)) (.split 2 (.split 1 (.leaf _ k2468_3) (.leaf _ k2468_4)) (.leaf _ k2468_5))) (.split 2 (.split 3 (.leaf _ k2468_6) (.split 1 (.leaf _ k2468_7) (.leaf _ k2468_8))) (.split 1 (.leaf _ k2468_9) (.leaf _ k2468_10)))))

end C4.Cert.Dir046

module

public import C4Check

public section

/-! Cells `4437 ≤ n < 4461` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir141

theorem c0 : allCells dirCell 4437 4454 [
    21168392611480937783655089047228330597736603495577506169289043462928093390329158529497217991377717917114371626270279669540166,
    44623917785954169965852543144435988408078598, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c1 : allCells dirCell 4454 4455 [
    1959177719132420001615599950046187817424983359931801372359251575998490654963614086565813649429329988424905210401573702970055623504421776200582772442213861181128153877255] = true := by
  decide +kernel

theorem k4455_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4455) 3).1 2).1
      1050530092220685952264366443676398295875687488109563344234565320230561044337637311353277318).isSome = true := by
  decide +kernel

theorem k4455_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4455) 3).1 2).2
      18921946095498987441117619904403689690913881958333075806240006672926050298008693417128575179374339004426055).isSome = true := by
  decide +kernel

theorem k4455_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4455) 3).2 2).1
      308184684211563684355643512682888623789414186613392039329695896442113993262219094878046763579279299319674265222).isSome = true := by
  decide +kernel

theorem k4455_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4455) 3).2 2).2
      261054300933884555629188954287458112046280818977944678134798165052350115001347484672349062).isSome = true := by
  decide +kernel

theorem k4456_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4456) 2).1 3).1 2).1
      63434817173859557586860215578519606676813580445703258505873073404215324724684668629809).isSome = true := by
  decide +kernel

theorem k4456_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4456) 2).1 3).1 2).2
      15861619952746874568180844794270209580820950470087655151939444461352288748347779538481).isSome = true := by
  decide +kernel

theorem k4456_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4456) 2).1 3).2 2).1
      252785734619702950067996909111824034148167535165885522613724814743797404970263931351857).isSome = true := by
  decide +kernel

theorem k4456_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4456) 2).1 3).2 2).2
      63177203338982120095098072678046051150112504152097684506562741769540189128513854206769).isSome = true := by
  decide +kernel

theorem k4456_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4456) 2).2 3).1 2).1
      15879003189485381550682525725955526988474857777130316601916296562400378019254194429489).isSome = true := by
  decide +kernel

theorem k4456_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4456) 2).2 3).1 2).2
      3440323929493290281758642802796349052680471618390614975238128079667).isSome = true := by
  decide +kernel

theorem k4456_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4456) 2).2 3).2 1).1
      252889348276047383972479269884714667356986206449836985758277842357945188547302442758962).isSome = true := by
  decide +kernel

theorem k4456_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4456) 2).2 3).2 1).2
      15815133083603235129791206493029922166892799474311619566640509480192555863593000867746).isSome = true := by
  decide +kernel

theorem k4457_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4457) 2).1 3).1 2).1
      1008159081015138978806352974830190389403965353613912598126453991810203936467451261644337).isSome = true := by
  decide +kernel

theorem k4457_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4457) 2).1 3).1 2).2
      1008398926727721819996764050298659064571834021385099688177263624294383393814822807522097).isSome = true := by
  decide +kernel

theorem k4457_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4457) 2).1 3).2 1).1
      16096167577219826726733339056375466493162473833119649861843885001019626322172061880315442).isSome = true := by
  decide +kernel

theorem k4457_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4457) 2).1 3).2 1).2
      62890595917578925915854508976305954999866801949880160932281521303616551195228533513442).isSome = true := by
  decide +kernel

theorem k4457_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4457) 2).2 3).1 1).1
      1009126523457821344944355838052773617457692503425698683177822514408997684299943555199794).isSome = true := by
  decide +kernel

theorem k4457_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4457) 2).2 3).1 1).2
      63052693205443909986042020065668587405571454988858302277567780753469018644346448731698).isSome = true := by
  decide +kernel

theorem k4457_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4457) 2).2 3).2 1).1
      4025663254045442611655371693816619288285655612383936652498213059818262422694002961009458).isSome = true := by
  decide +kernel

theorem k4457_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4457) 2).2 3).2 1).2
      62886962882908782332902907722124625135810455884337032074766279238135734318552549383730).isSome = true := by
  decide +kernel

theorem k4458_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4458) 2).1 3).1 1).1
      1003869142512150631035378590350416851190756117149995480621622962309658488042311796497202).isSome = true := by
  decide +kernel

theorem k4458_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4458) 2).1 3).1 1).2
      15682014879301178820974429563876514146794716931150141039165775081515726755367609505586).isSome = true := by
  decide +kernel

theorem k4458_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4458) 2).1 3).2 1).1
      250537793894908433356545490366797552868426926333957323714317690278142359380463108053810).isSome = true := by
  decide +kernel

theorem k4458_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4458) 2).1 3).2 1).2
      3914064436707333391940829465262614320230927464722774719207376518703412967333874685746).isSome = true := by
  decide +kernel

theorem k4458_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4458) 2).2 3).1 1).1
      3924547986507195943287150986235843767487049553568473270628033854874545909589127715532).isSome = true := by
  decide +kernel

theorem k4458_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4458) 2).2 3).1 1).2
      15687051994395943134117998978314638564701459693694478294397992043739627491454076538572).isSome = true := by
  decide +kernel

theorem k4458_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4458) 2).2 3).2 1).1
      3915864544144841702048168185290536284667512127433198699901237945769638749587721673420).isSome = true := by
  decide +kernel

theorem k4458_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4458) 2).2 3).2 1).2
      15662071768951498135741648245989140019938057200946820807135569769852620647624151799602).isSome = true := by
  decide +kernel

theorem k4459_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4459) 2).1 3).1 1).1
      977296407324334080069048802132001811037492417311397069549942159592186945119289441068).isSome = true := by
  decide +kernel

theorem k4459_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4459) 2).1 3).1 1).2
      244287825549087857226443566566517036044017614120329621708381739976491520027442765612).isSome = true := by
  decide +kernel

theorem k4459_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4459) 2).1 3).2 1).1
      3307662762836901327341405951742812107594307962889061045040996140).isSome = true := by
  decide +kernel

theorem k4459_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4459) 2).1 3).2 1).2
      244030065347628644044671359844956037998880468770968572727309184298937266761016762156).isSome = true := by
  decide +kernel

theorem k4459_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4459) 2).2 3).1
      87192515012167357748495718262747747844578618159390896045933651195554782040492126404594261410173021238697849863006194196798729009).isSome = true := by
  decide +kernel

theorem k4459_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4459) 2).2 3).2
      18886256138627401589712515944145178105234454254498344634707606355445767049104865874111959567229821293523586865).isSome = true := by
  decide +kernel

theorem k4460_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4460) 2).1 3).1
      73689358636195139539096356305623713053060708047140372894979151512107130662594539011967275360454645724576945).isSome = true := by
  decide +kernel

theorem k4460_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4460) 2).1 3).2
      73639149407240767847192643822523177028378427318876278881613790405885639939509204157418294821353326950841521).isSome = true := by
  decide +kernel

theorem k4460_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4460) 2).2 3).1
      1022927955399648129480943388627195808131413960426012850993176912517028044118303103062831345).isSome = true := by
  decide +kernel

theorem k4460_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4460) 2).2 3).2
      294628289692817665981463281365788653717710683704963409118572184922803146234263065298270800214265186501390577).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4437 4461 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.one (box := dirCellBox) (n := 4455)
      (.split 3 (.split 2 (.leaf _ k4455_0) (.leaf _ k4455_1)) (.split 2 (.leaf _ k4455_2) (.leaf _ k4455_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4456)
      (.split 2 (.split 3 (.split 2 (.leaf _ k4456_0) (.leaf _ k4456_1)) (.split 2 (.leaf _ k4456_2) (.leaf _ k4456_3))) (.split 3 (.split 2 (.leaf _ k4456_4) (.leaf _ k4456_5)) (.split 1 (.leaf _ k4456_6) (.leaf _ k4456_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4457)
      (.split 2 (.split 3 (.split 2 (.leaf _ k4457_0) (.leaf _ k4457_1)) (.split 1 (.leaf _ k4457_2) (.leaf _ k4457_3))) (.split 3 (.split 1 (.leaf _ k4457_4) (.leaf _ k4457_5)) (.split 1 (.leaf _ k4457_6) (.leaf _ k4457_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4458)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4458_0) (.leaf _ k4458_1)) (.split 1 (.leaf _ k4458_2) (.leaf _ k4458_3))) (.split 3 (.split 1 (.leaf _ k4458_4) (.leaf _ k4458_5)) (.split 1 (.leaf _ k4458_6) (.leaf _ k4458_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4459)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4459_0) (.leaf _ k4459_1)) (.split 1 (.leaf _ k4459_2) (.leaf _ k4459_3))) (.split 3 (.leaf _ k4459_4) (.leaf _ k4459_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4460)
      (.split 2 (.split 3 (.leaf _ k4460_0) (.leaf _ k4460_1)) (.split 3 (.leaf _ k4460_2) (.leaf _ k4460_3))))

end C4.Cert.Dir141

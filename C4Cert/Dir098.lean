module

public import C4Check

public section

/-! Cells `3227 ≤ n < 3251` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir098

theorem k3227_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3227) 2).1 3).1
      6426624438819357977782708594224503980116623619001342378680684244140819447236999847784350662485648360549283168207322051408378401660477004702715556668).isSome = true := by
  decide +kernel

theorem k3227_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3227) 2).1 3).2
      62431526513574574425646854747158783412470374404070740888171664886970698217087879861052).isSome = true := by
  decide +kernel

theorem k3227_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3227) 2).2 3).1
      18893830036667375562675910731308851426718225951221275376304868989816803911154384128412665483099931116729836348).isSome = true := by
  decide +kernel

theorem k3227_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3227) 2).2 3).2
      15615062836668285220792711976561805677077072544279726127515796591438568607853785371452).isSome = true := by
  decide +kernel

theorem k3228_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3228) 2).1 3).1
      287691829435774127385294705344908730601401934716144483912467337617964819340745543211616602019557092610876).isSome = true := by
  decide +kernel

theorem k3228_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3228) 2).1 3).2
      287514554660208018687481907863379634140100454192498819058805766301485254351101390009803773414064814281532).isSome = true := by
  decide +kernel

theorem k3228_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3228) 2).2 3).1
      15601613267073923072847790273000082717673762005667129088659570471789252009083534824252).isSome = true := by
  decide +kernel

theorem k3228_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3228) 2).2 3).2
      15590770987953356060357936224518879821494013552524435714974465871486921812096058783292).isSome = true := by
  decide +kernel

theorem k3229_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3229) 3).1 2).1
      60856222975313707404730283860690453385714484856549106759954440529370448500856577340).isSome = true := by
  decide +kernel

theorem k3229_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3229) 3).1 2).2
      71859631183959248472073277741484059756121251087130917954415557323892298709974787190508583834172863673916).isSome = true := by
  decide +kernel

theorem k3229_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3229) 3).2
      339212859467223444416840086810052535641290115310825508381393659012226133559632992263357091711131831719943837539779543229887730).isSome = true := by
  decide +kernel

theorem k3230_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3230) 2).1
      338932203389921944958949920779245133392740802317139378273381814783246473630224713020012714967464627247633613283378208381170931).isSome = true := by
  decide +kernel

theorem k3230_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3230) 2).2
      339010543719714316963198232649389430834693281719244579109833946109979789774324439373398226143134215211221954944808712401417457).isSome = true := by
  decide +kernel

theorem k3231_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3231) 2).1
      15193129878597274479596033198041876354325477155046958981109031272688474556244971889).isSome = true := by
  decide +kernel

theorem k3231_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3231) 2).2
      5294538641711584191936451043875918561436166516048021332061330951319448908312834219883477683757310399828190046541921281103676).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 3232 3233 [
    6248298584143237959932611579712954810738911009078692707919851201413992563165121258589464237924480600368991143379700410557910828601541824031815110] = true := by
  decide +kernel

theorem c6 : allCells dirCell 3233 3250 [
    60737637882557010689825668068920453742915206116400347373686794295433917135273425266,
    2788354150360104528940943166530973598930690, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3250_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3250) 3).1
      160530764913593644552291).isSome = true := by
  decide +kernel

theorem k3250_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3250) 3).2
      123416780010067769456527825028132658011335580606955883455068143243704185072568592804242420585154205488207690042769909534001245040552682628615870668324144834999235531035).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3227 3251 :=
  (Cover.one (box := dirCellBox) (n := 3227)
      (.split 2 (.split 3 (.leaf _ k3227_0) (.leaf _ k3227_1)) (.split 3 (.leaf _ k3227_2) (.leaf _ k3227_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3228)
      (.split 2 (.split 3 (.leaf _ k3228_0) (.leaf _ k3228_1)) (.split 3 (.leaf _ k3228_2) (.leaf _ k3228_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3229)
      (.split 3 (.split 2 (.leaf _ k3229_0) (.leaf _ k3229_1)) (.leaf _ k3229_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3230)
      (.split 2 (.leaf _ k3230_0) (.leaf _ k3230_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3231)
      (.split 2 (.leaf _ k3231_0) (.leaf _ k3231_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 3250)
      (.split 3 (.leaf _ k3250_0) (.leaf _ k3250_1)))

end C4.Cert.Dir098

module

public import C4Check

public section

/-! Cells `3251 ≤ n < 3255` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir099

theorem k3251_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3251) 3).1 2).1 1).1
      15729143530844553755685898050306249923143251552277735620622048953373427002453279091).isSome = true := by
  decide +kernel

theorem k3251_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3251) 3).1 2).1 1).2
      4639832500316085045712320572363076223002214188492056141923785501350532366659786975083962359339727551859).isSome = true := by
  decide +kernel

theorem k3251_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3251) 3).1 2).2
      21912888898737347352259884927061880241154944116550987864554959157710593275636857311233532203350160756565710322366675017561677).isSome = true := by
  decide +kernel

theorem k3251_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3251) 3).2 2).1 1).1
      4002232430585423432225165562915713504618378668207179610325967365544180184016739619644).isSome = true := by
  decide +kernel

theorem k3251_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3251) 3).2 2).1 1).2
      13878658362713175843971114727878985852888079967652554767548802862652).isSome = true := by
  decide +kernel

theorem k3251_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3251) 3).2 2).2
      1392338042757852258134434401081934129195318405599139468146798759975611345300713982279029379803872502382467287112433623000249587).isSome = true := by
  decide +kernel

theorem k3252_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3252) 3).1 2).1 1).1
      215570019075485075032025531864499341827163430828159279796099467836).isSome = true := by
  decide +kernel

theorem k3252_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3252) 3).1 2).1 1).2
      13468841322424379741514257174749302188312341745244893902278327356).isSome = true := by
  decide +kernel

theorem k3252_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3252) 3).1 2).2
      26184436238985792855620260930556002673961922265655064676984032405688910768590445985793151444734237147037572800570469776814955351625070225190306001724).isSome = true := by
  decide +kernel

theorem k3252_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3252) 3).2 2).1
      5646831054191720332984878140990065874686410293500871868226182366358627221855349265095801153360382645934400698294954474903002663153).isSome = true := by
  decide +kernel

theorem k3252_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3252) 3).2 2).2
      88295499000448664508472181913586377935483192583983804533337959918229533256659066986413884414355295115908156357296740161208435516).isSome = true := by
  decide +kernel

theorem k3253_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3253) 3).1 2).1
      4878632955817940289214449667661624564493102051480722535936996434335073438728740852193209540489940492814245032177).isSome = true := by
  decide +kernel

theorem k3253_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3253) 3).1 2).2
      76295895584727369197177393143390660754641140933718749325099630892065835198055280452816234538888342565740856124).isSome = true := by
  decide +kernel

theorem k3253_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3253) 3).2 2).1
      304031715074001673146002478804609362465909291949361912587935278192341197062187397309059421203688597869874770161).isSome = true := by
  decide +kernel

theorem k3253_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3253) 3).2 2).2
      297174605784964528444483489126923285810586286538681974189091590747790309146872759959768226383397659667135548).isSome = true := by
  decide +kernel

theorem k3254_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3254) 2).1 3).1
      4741148504849917828809835050455349542812231023454596640511038652748108634497977382333704354602328967907099452).isSome = true := by
  decide +kernel

theorem k3254_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3254) 2).1 3).2
      4733056302720751950511514755330084453067660009237545448699772286880801398304085783103212339422061248703873852).isSome = true := by
  decide +kernel

theorem k3254_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3254) 2).2 3).1
      296504804815649425771025652115889213090555653498443302043640998261983842283278101533560968141416755960806460).isSome = true := by
  decide +kernel

theorem k3254_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3254) 2).2 3).2
      295949739364005928200596439024287907084352336356863768856548927686733280751376212860703730732688997266816060).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3251 3255 :=
  (Cover.one (box := dirCellBox) (n := 3251)
      (.split 3 (.split 2 (.split 1 (.leaf _ k3251_0) (.leaf _ k3251_1)) (.leaf _ k3251_2)) (.split 2 (.split 1 (.leaf _ k3251_3) (.leaf _ k3251_4)) (.leaf _ k3251_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3252)
      (.split 3 (.split 2 (.split 1 (.leaf _ k3252_0) (.leaf _ k3252_1)) (.leaf _ k3252_2)) (.split 2 (.leaf _ k3252_3) (.leaf _ k3252_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3253)
      (.split 3 (.split 2 (.leaf _ k3253_0) (.leaf _ k3253_1)) (.split 2 (.leaf _ k3253_2) (.leaf _ k3253_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3254)
      (.split 2 (.split 3 (.leaf _ k3254_0) (.leaf _ k3254_1)) (.split 3 (.leaf _ k3254_2) (.leaf _ k3254_3))))

end C4.Cert.Dir099

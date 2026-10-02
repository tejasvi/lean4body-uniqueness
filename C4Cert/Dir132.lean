module

public import C4Check

public section

/-! Cells `3952 ≤ n < 3979` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir132

theorem k3952_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3952) 2).1
      737671126014108077733492516429437979971058479371).isSome = true := by
  decide +kernel

theorem k3952_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3952) 2).2 3).1
      985811389833981571816650708799887003892780898563467260620379659054056629169756427718).isSome = true := by
  decide +kernel

theorem k3952_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3952) 2).2 3).2
      982106321602451291285723877183095641081917396014386629801379295838781651420430652870).isSome = true := by
  decide +kernel

theorem k3953_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3953) 2).1
      183751664648429639142347617152879405457617195275).isSome = true := by
  decide +kernel

theorem k3953_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3953) 2).2
      87185726559268130329270332774974377986800521587971043658846180232889559425270314627025221623104594901972491906710268010128938267).isSome = true := by
  decide +kernel

theorem k3954_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3954) 2).1
      183424565926254909624139417219377148194342456331).isSome = true := by
  decide +kernel

theorem k3954_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3954) 2).2
      21242014265066245433933677279928863201519356212274300641884278770553049366503532441205532636901054587851984787336871678453191).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3955 3956 [
    1892656403670676863829752287526983138023705343882922787799820902424865085217878773400837367519515731581122579133298974834209041944207488231071179887068359215071179445002] = true := by
  decide +kernel

theorem c4 : allCells dirCell 3956 3977 [
    52777550829501955508616459371154240888203842941886189786859884994, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3977_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3977) 3).1
      43262307414783669289632227).isSome = true := by
  decide +kernel

theorem k3977_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3977) 3).2 3).1 2).1
      6839005203841324843525233580658215205014343534566406207879227858669915536607939700340017965522524889159478004595375829164509618293627112754645319).isSome = true := by
  decide +kernel

theorem k3977_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3977) 3).2 3).1 2).2
      66792890288852264564123588657187386662741203734674571720944591067059564885235024454).isSome = true := by
  decide +kernel

theorem k3977_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3977) 3).2 3).2 2).1
      6755937329618180612909397542626755424209995948724058520109969247837249626291409070349875258375666979486466803392851156471966131423635291847128518).isSome = true := by
  decide +kernel

theorem k3977_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3977) 3).2 3).2 2).2
      262758424411548255513502215867021351286993071356502705163682416088217758184330200390).isSome = true := by
  decide +kernel

theorem k3978_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).1 2).1 3).1
      66400180093552680974428693121350315297026457729477864442769741287811560374724059210950).isSome = true := by
  decide +kernel

theorem k3978_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).1 2).1 3).2
      65694298230361163178511352905317672286506524480982930149065774699300710338707975582918).isSome = true := by
  decide +kernel

theorem k3978_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).1 2).2 3).1
      1062890931721218783848905310768982104597110887546449623702264056876841012541727686021830).isSome = true := by
  decide +kernel

theorem k3978_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).1 2).2 3).2
      1052848089753408510494472278864641559400218950533169075899553018705525145949005630678214).isSome = true := by
  decide +kernel

theorem k3978_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).1 2).1
      64560502590711902202474695506080356595119413396713512895543515524667894138449266095303).isSome = true := by
  decide +kernel

theorem k3978_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).1 2).2
      64643856018288306238771288872521352247403053142785005360103335277226072527310444143821).isSome = true := by
  decide +kernel

theorem k3978_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).2 3).1
      1043483161372172728273699595556133444117291599244948851960013722073963253755859295847625).isSome = true := by
  decide +kernel

theorem k3978_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3978) 3).2 2).2 3).2
      259048739175219831737426121777317171806449669362894985225064321354757037333633787491526).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3952 3979 :=
  (Cover.one (box := dirCellBox) (n := 3952)
      (.split 2 (.leaf _ k3952_0) (.split 3 (.leaf _ k3952_1) (.leaf _ k3952_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3953)
      (.split 2 (.leaf _ k3953_0) (.leaf _ k3953_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3954)
      (.split 2 (.leaf _ k3954_0) (.leaf _ k3954_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 3977)
      (.split 3 (.leaf _ k3977_0) (.split 3 (.split 2 (.leaf _ k3977_1) (.leaf _ k3977_2)) (.split 2 (.leaf _ k3977_3) (.leaf _ k3977_4))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3978)
      (.split 3 (.split 2 (.split 3 (.leaf _ k3978_0) (.leaf _ k3978_1)) (.split 3 (.leaf _ k3978_2) (.leaf _ k3978_3))) (.split 2 (.split 2 (.leaf _ k3978_4) (.leaf _ k3978_5)) (.split 3 (.leaf _ k3978_6) (.leaf _ k3978_7)))))

end C4.Cert.Dir132

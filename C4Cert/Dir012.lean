module

public import C4Check

public section

/-! Cells `1573 ≤ n < 1602` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir012

theorem k1573_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).1 3).1 2).1
      18056030379326943267873739492380634846750746134438776713693610896086285181245787955288036540741177356657).isSome = true := by
  decide +kernel

theorem k1573_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).1 3).1 2).2
      61169810652551547919645775766302945208738690268794962055219217204486442141837599089).isSome = true := by
  decide +kernel

theorem k1573_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).1 3).2 2).1
      244318588585009987228419753808831096040485396593143395336161028091684117756712699981).isSome = true := by
  decide +kernel

theorem k1573_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).1 3).2 2).2
      62557289632415160014962950456923595476241719733301528214525158877573235680497163521613).isSome = true := by
  decide +kernel

theorem k1573_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1573) 2).2 3).1
      100717939894785954727235209180953326485222570260758690173221853472748842595785108002508213537359305679858853377915600788571479467613305577592047046).isSome = true := by
  decide +kernel

theorem k1573_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).2 3).2 2).1
      977874092687119561242509870779559544986036378914111128009394751928209474885987729997).isSome = true := by
  decide +kernel

theorem k1573_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1573) 2).2 3).2 2).2
      244529998255424707333463689730799962950475291056512949263678174739126330033122880881).isSome = true := by
  decide +kernel

theorem k1574_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1574) 2).1 2).1
      21245847301780297003443832210410690750703730247367407323022089239281224667952007252485516984840353372459669109793818253952455).isSome = true := by
  decide +kernel

theorem k1574_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1574) 2).1 2).2
      25081940262911430217883623400365558786445842778053749796406011816471629810163601335575778750893377882426356696071821345282822013553687677365966135).isSome = true := by
  decide +kernel

theorem k1574_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1574) 2).2 3).1 2).1
      3906296336183191545069520445147654470421909069858863006711569439582514751148897359665).isSome = true := by
  decide +kernel

theorem k1574_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1574) 2).2 3).1 2).2
      3907459816913237787164849899280202744302309479995472631603215973967975603173479651121).isSome = true := by
  decide +kernel

theorem k1574_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1574) 2).2 3).2
      348094584308228827303573389791453498326013206846730146265408576220002697400618094219492913054280036558515281407800793563653542598).isSome = true := by
  decide +kernel

theorem k1575_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1575) 2).1
      844871046208336148203574148301768834505623955089229422408181292038).isSome = true := by
  decide +kernel

theorem k1575_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1575) 2).2 2).1
      71880347854400675117829525763156257624204062290500757343508828892415572216527683249267299577717026653639).isSome = true := by
  decide +kernel

theorem k1575_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1575) 2).2 2).2
      339467608406784999165657003716346971311837830529681802817051579612112199391583861212241807910739786677960864491953480273458375).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 1576 1578 [
    6405861129382257383741688167814814019274216332614732664304305980835384793949389760991157944191176068462085366423782139616282174086464850221541477894,
    2420755916586998554234978] = true := by
  decide +kernel

theorem c4 : allCells dirCell 1578 1601 [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    47365880394309193081579190337046225759068704752611] = true := by
  decide +kernel

theorem k1601_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1601) 3).1 2).1
      289353933861999865399855574004708648885615934577338797246016078533867553546005990170251670751627873785607).isSome = true := by
  decide +kernel

theorem k1601_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1601) 3).1 2).2
      289671606799231356487687170727792697325139035716344074007695082805533590484523204803055031679403667396359).isSome = true := by
  decide +kernel

theorem k1601_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1601) 3).2 2).1
      6438617666799236942518562693054389870441618170847134589654929062917779191468730936112429065465104494837119554418602784598337422861047606604493809991).isSome = true := by
  decide +kernel

theorem k1601_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1601) 3).2 2).2
      100680902612832411450645857311339529204657476716009545282856892800083850965972445347270614368316295009063488315803240303092407376523744540773978439).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1573 1602 :=
  (Cover.one (box := dirCellBox) (n := 1573)
      (.split 2 (.split 3 (.split 2 (.leaf _ k1573_0) (.leaf _ k1573_1)) (.split 2 (.leaf _ k1573_2) (.leaf _ k1573_3))) (.split 3 (.leaf _ k1573_4) (.split 2 (.leaf _ k1573_5) (.leaf _ k1573_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1574)
      (.split 2 (.split 2 (.leaf _ k1574_0) (.leaf _ k1574_1)) (.split 3 (.split 2 (.leaf _ k1574_2) (.leaf _ k1574_3)) (.leaf _ k1574_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1575)
      (.split 2 (.leaf _ k1575_0) (.split 2 (.leaf _ k1575_1) (.leaf _ k1575_2)))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 1601)
      (.split 3 (.split 2 (.leaf _ k1601_0) (.leaf _ k1601_1)) (.split 2 (.leaf _ k1601_2) (.leaf _ k1601_3))))

end C4.Cert.Dir012

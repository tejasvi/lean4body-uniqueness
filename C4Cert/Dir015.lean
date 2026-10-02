module

public import C4Check

public section

/-! Cells `1657 ≤ n < 1665` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir015

theorem k1657_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1657) 3).1
      85883086028539688097937971707675760070088967412281175256276598932819442941296446718496093772681403453260326146160580213135942).isSome = true := by
  decide +kernel

theorem k1657_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1657) 3).2 2).1
      72488274930240473633457483250883043059802778127485883487909991929326882556868969657780429638252707857777).isSome = true := by
  decide +kernel

theorem k1657_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1657) 3).2 2).2
      72530712920978215410496599728215811233690311476368869308498167275469587016016654189945374608521097905521).isSome = true := by
  decide +kernel

theorem k1658_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1658) 3).1 2).1
      1156759631793810874562965507445253931572941068762717579771531081140406266602993346814992780229678967512497).isSome = true := by
  decide +kernel

theorem k1658_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1658) 3).1 2).2
      4629503422042816868493678610057995398487579317545225639652411344755349072927670979472136010182266172729933).isSome = true := by
  decide +kernel

theorem k1658_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1658) 3).2 2).1
      250304757219755480316736894919857197252860801339851329120003914101156947782319970546355).isSome = true := by
  decide +kernel

theorem k1658_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1658) 3).2 2).2
      62633711543803263820918253629918388441438629499710206878643432561578821435123331718321).isSome = true := by
  decide +kernel

theorem k1659_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1659) 3).1 2).1
      4612969679817764197775893287049772201289904996710832420254564346569689116515400055783411758508284617889585).isSome = true := by
  decide +kernel

theorem k1659_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1659) 3).1 2).2
      3909421106978197926550976956913615689612633458535883689179810166193490147964795017009).isSome = true := by
  decide +kernel

theorem k1659_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1659) 3).2 2).1
      249711807352237750901641798047522849714279865060277782919649830925980986706255038420785).isSome = true := by
  decide +kernel

theorem k1659_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1659) 3).2 2).2
      4609520904472761933625938972180819956041663407038107166891878535564598312690557196686580650782132760467249).isSome = true := by
  decide +kernel

theorem k1660_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1660) 3).1 2).1
      998065309978139640948414159917064747796725730729772891414928275851348460227249722192689).isSome = true := by
  decide +kernel

theorem k1660_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1660) 3).1 2).2
      1151330397567812385317059692250587446466041641741231678445788552191254282065212594660112134168180001039308).isSome = true := by
  decide +kernel

theorem k1660_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1660) 3).2 1).1
      974147112171357212282082411107733208523327599358405880633780876604787817765391924428).isSome = true := by
  decide +kernel

theorem k1660_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1660) 3).2 1).2
      3897030702096419833155320529828282329818267594234533807588964144708720187239713586380).isSome = true := by
  decide +kernel

theorem k1661_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1661) 3).1
      22230579971402658410405605856390723164675897216921068285008903865598747084194596809178211886474485393349180233423589862450151093041).isSome = true := by
  decide +kernel

theorem k1661_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1661) 3).2
      3985785497849230540567319969781724672791729485791892200081175434515494934256507121158962).isSome = true := by
  decide +kernel

theorem k1662_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1662) 3).1
      3983979569224662181204852843323963494208927951095145293610471788754635084009016825072434).isSome = true := by
  decide +kernel

theorem k1662_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1662) 3).2
      3982497111822633946813335144294539892560545593709702733528275312252835127925087363517234).isSome = true := by
  decide +kernel

theorem k1663_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1663) 2).1
      995177395523833096718055844248905708772067807595841302227385109929213457712660532898611).isSome = true := by
  decide +kernel

theorem k1663_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1663) 2).2
      248795297102549367134053552626476491722788103029088974462514658830248353764954635356979).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 1664 1665 [
    1598274598331598485782864344315530454518393578826904009374040399374325536492640786862568418112022980462967347337015549998180881829731233628991788486] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1657 1665 :=
  (Cover.one (box := dirCellBox) (n := 1657)
      (.split 3 (.leaf _ k1657_0) (.split 2 (.leaf _ k1657_1) (.leaf _ k1657_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1658)
      (.split 3 (.split 2 (.leaf _ k1658_0) (.leaf _ k1658_1)) (.split 2 (.leaf _ k1658_2) (.leaf _ k1658_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1659)
      (.split 3 (.split 2 (.leaf _ k1659_0) (.leaf _ k1659_1)) (.split 2 (.leaf _ k1659_2) (.leaf _ k1659_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1660)
      (.split 3 (.split 2 (.leaf _ k1660_0) (.leaf _ k1660_1)) (.split 1 (.leaf _ k1660_2) (.leaf _ k1660_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1661)
      (.split 3 (.leaf _ k1661_0) (.leaf _ k1661_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1662)
      (.split 3 (.leaf _ k1662_0) (.leaf _ k1662_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1663)
      (.split 2 (.leaf _ k1663_0) (.leaf _ k1663_1))).trans <|
  (Cover.dir c7)

end C4.Cert.Dir015

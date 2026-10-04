module

public import C4Check

public section

/-! Cells `2776 ≤ n < 2777` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir062

theorem k2776_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).1 3).1 1).1
      1009210525978767665835842233715116054385014902429113495463948598239792464517899808774963).isSome = true := by
  decide +kernel

theorem k2776_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).1 3).1 1).2
      18623531729599733702387670733072654665074251817677511275385077424570075489791765859136490845982417216860732).isSome = true := by
  decide +kernel

theorem k2776_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).1 3).2 1).1
      290502081361878441248486114237464183178187996369601518908584671721217253746545209919097084623445347916748).isSome = true := by
  decide +kernel

theorem k2776_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).1 3).2 1).2
      983839877533216984788346105969159759279171060063999409647462961078051491422788747052).isSome = true := by
  decide +kernel

theorem k2776_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).2 1).1 3).1
      16188812068126871332084956220944662013397384638561239604490647426948393362884255113695025).isSome = true := by
  decide +kernel

theorem k2776_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).2 1).1 3).2
      15762227923977451422846523139910145712425493459820894428670901170595763208087702719436).isSome = true := by
  decide +kernel

theorem k2776_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).2 1).2 3).1
      18645335056523066829292605883347795399786749120300241046486149599535136040114243734617576199418231179951164).isSome = true := by
  decide +kernel

theorem k2776_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).1 2).2 1).2 3).2
      252080926234437752596215207064355433208705830313686154084299134679888433828260129995836).isSome = true := by
  decide +kernel

theorem k2776_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).2 2).1 1).1
      350088669806975090706704200666609136153702609522254520018147676806682705237035012863916832468793475757529405729486620775491927219).isSome = true := by
  decide +kernel

theorem k2776_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).2 2).1 1).2 3).1
      13309591030604293395740927736427428709941685074955458934092692652).isSome = true := by
  decide +kernel

theorem k2776_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).2 2).1 1).2 3).2
      13291095188668052510230792843676380279078051597479999261925538988).isSome = true := by
  decide +kernel

theorem k2776_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).2 2).2 3).1 1).1
      53306871086749198250417586832035251957043211579197142524741906124).isSome = true := by
  decide +kernel

theorem k2776_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).2 2).2 3).1 1).2
      53337003406414060690589525424455826833708919534562067016868819516).isSome = true := by
  decide +kernel

theorem k2776_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).1 3).2 2).2 3).2
      21886488421312609265500623682199736615254860816283132748150845223447269162162548792811303473948567280443809197380964200523128625).isSome = true := by
  decide +kernel

theorem k2776_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).1 2).1 1).1
      18693733891238062055817625710269704415611958046670145902588723203054500268747861362356125167539581634853948).isSome = true := by
  decide +kernel

theorem k2776_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).1 2).1 1).2
      74663958803527952809319204513827484684785517589308468217072496006283697900076967534167562828271024281664572).isSome = true := by
  decide +kernel

theorem k2776_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).1 2).2 1).1
      63404638744537235557841417908339053884278034616263961455056777883340367515533601733692).isSome = true := by
  decide +kernel

theorem k2776_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).1 2).2 1).2
      13742423278856524050267868765523442085321666122861214243487433014332).isSome = true := by
  decide +kernel

theorem k2776_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).2 2).1 1).1
      213833895137753353893194976236236682786255576472698467858321361868).isSome = true := by
  decide +kernel

theorem k2776_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).2 2).1 1).2
      15772270702165167342061112026250334684851583031988508134625037708993308414013056334908).isSome = true := by
  decide +kernel

theorem k2776_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).2 2).2 1).1
      15796046805690335823320183542729021616137560876581070918187114351572749864174310243388).isSome = true := by
  decide +kernel

theorem k2776_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).1 3).2 2).2 1).2
      15788956530402694714955784818613229390945489015281039220263602471456886096591849372732).isSome = true := by
  decide +kernel

theorem k2776_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).2 3).1 2).1 1).1
      13365538102807639196227306526985699212550128782690707766731497164).isSome = true := by
  decide +kernel

theorem k2776_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).2 3).1 2).1 1).2
      15740546904649207540081041984329899557512717084371917844252606360030303229833409051708).isSome = true := by
  decide +kernel

theorem k2776_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).2 3).1 2).2 1).1
      53400663516483805168323927022075997393464465916141213822122290892).isSome = true := by
  decide +kernel

theorem k2776_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).2 3).1 2).2 1).2
      15754852510700403426151564210134661746332939819527857670012779260180265153942316235836).isSome = true := by
  decide +kernel

theorem k2776_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).2 3).2 2).1
      18998588515047724914885882403041445180528104083621866314308874383936466299498787036742012577221071881861934897).isSome = true := by
  decide +kernel

theorem k2776_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2776) 2).2 3).2 3).2 2).2
      1402849346942349664899794539046833007317769970185528933400379151056513567892192891130653730577535765176378890975912345532251077425).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2776 2777 :=
  (Cover.one (box := dirCellBox) (n := 2776)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2776_0) (.leaf _ k2776_1)) (.split 1 (.leaf _ k2776_2) (.leaf _ k2776_3))) (.split 1 (.split 3 (.leaf _ k2776_4) (.leaf _ k2776_5)) (.split 3 (.leaf _ k2776_6) (.leaf _ k2776_7)))) (.split 2 (.split 1 (.leaf _ k2776_8) (.split 3 (.leaf _ k2776_9) (.leaf _ k2776_10))) (.split 3 (.split 1 (.leaf _ k2776_11) (.leaf _ k2776_12)) (.leaf _ k2776_13)))) (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k2776_14) (.leaf _ k2776_15)) (.split 1 (.leaf _ k2776_16) (.leaf _ k2776_17))) (.split 2 (.split 1 (.leaf _ k2776_18) (.leaf _ k2776_19)) (.split 1 (.leaf _ k2776_20) (.leaf _ k2776_21)))) (.split 3 (.split 2 (.split 1 (.leaf _ k2776_22) (.leaf _ k2776_23)) (.split 1 (.leaf _ k2776_24) (.leaf _ k2776_25))) (.split 2 (.leaf _ k2776_26) (.leaf _ k2776_27))))))

end C4.Cert.Dir062

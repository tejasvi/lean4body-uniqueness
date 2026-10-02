module

public import C4Check

public section

/-! Cells `3557 ≤ n < 3558` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir112

theorem k3557_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3557) 3).1 3).1
      10651477879419392220277683153147736720409324720858815842846017135646).isSome = true := by
  decide +kernel

theorem k3557_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).1 3).2 2).1 3).1
      277024396195053901995290852722106490219603700455534074345533158925364295048712128073).isSome = true := by
  decide +kernel

theorem k3557_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).1 3).2 2).1 3).2
      23779230447904029430608939398290190366350313033252766729600435663126510715564357191266465867019111505275193704197389104453065).isSome = true := by
  decide +kernel

theorem k3557_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3557) 3).1 3).2 2).2
      1523990313079324781669232686070909065773059013291378085856575232834933493563426139983789686462920767624211065193850121402643483).isSome = true := by
  decide +kernel

theorem k3557_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).1 2).1
      440544622214122846486696305243018520485259429659214285604181616447485859086406183429246621281766862465612595303852828048335616083557429417506153933).isSome = true := by
  decide +kernel

theorem k3557_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).1 2).2
      95660513062214897274211527439893717868606324128280686536565815411290273144070521136980002163120142058112656113243398124057605573).isSome = true := by
  decide +kernel

theorem k3557_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).2 2).1
      27637511598555938479363274518907986427750127618327662977450108805942411941338665851491554356375931904789413014460564087691423165868764022969072573637).isSome = true := by
  decide +kernel

theorem k3557_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).2 2).2
      5086316907877586044761185133429306120333633872014589463527875175305290165516020799924526048333740695021509833).isSome = true := by
  decide +kernel

theorem k3557_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).2 3).1
      32574796798670912391772722411787653486623685121092959539348881607752550669859359574121636973272798423851143125167674081906625346706705162948430866406021406604892517657).isSome = true := by
  decide +kernel

theorem k3557_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).2 3).2 2).1
      4972116827715739718697774657401871143835131477418639336562454331872556357360516919718767799094347919095025).isSome = true := by
  decide +kernel

theorem k3557_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).2 3).2 2).2
      310918184676345494301483939440157813820026705335427405097247007342945841251809100358915977948481666766705).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3557 3558 :=
  (Cover.one (box := dirCellBox) (n := 3557)
      (.split 3 (.split 3 (.leaf _ k3557_0) (.split 2 (.split 3 (.leaf _ k3557_1) (.leaf _ k3557_2)) (.leaf _ k3557_3))) (.split 2 (.split 3 (.split 2 (.leaf _ k3557_4) (.leaf _ k3557_5)) (.split 2 (.leaf _ k3557_6) (.leaf _ k3557_7))) (.split 3 (.leaf _ k3557_8) (.split 2 (.leaf _ k3557_9) (.leaf _ k3557_10))))))

end C4.Cert.Dir112

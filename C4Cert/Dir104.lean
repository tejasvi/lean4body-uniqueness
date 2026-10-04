module

public import C4Check

public section

/-! Cells `3530 ≤ n < 3531` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir104

theorem k3530_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).1 3).1 2).1
      259128700557875208697074494376669951653584245370146232572538833501137991472268138927895).isSome = true := by
  decide +kernel

theorem k3530_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).1 3).1 2).2
      1225916333146180515387730807434801024005893273616172024589362433097005435873077826690428549729160185518566167).isSome = true := by
  decide +kernel

theorem k3530_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).1 3).2 2).1
      3477596551381948277793984897922523576388511592303781683632408123159).isSome = true := by
  decide +kernel

theorem k3530_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).1 3).2 2).2
      1399418414932840558335178479124556330644000999249186222112073039369135181175415610462446126385811106607575655145457802828863255).isSome = true := by
  decide +kernel

theorem k3530_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).2 3).1 2).1
      894443070904652520314580575657675595400247335450892898731979383215703206287195020560570943795897871466323485).isSome = true := by
  decide +kernel

theorem k3530_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).2 3).1 2).2
      22731756003991831730752031626944667138559069130353741402810228806725054922254482414517488378403784112994471193731651343825788445).isSome = true := by
  decide +kernel

theorem k3530_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).2 3).2 2).1
      773114315391698615536651658169440435944985985470461818244614803408039321862280161866107671).isSome = true := by
  decide +kernel

theorem k3530_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).2 3).2 2).2
      4131622312389819509796540129754372745093759776778201365042882859125224439445061180672797).isSome = true := by
  decide +kernel

theorem k3530_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).2 2).1 3).1
      77259955142645087983467878043610385751826706369510430491166394223484985084867819266902954390940573833336108246).isSome = true := by
  decide +kernel

theorem k3530_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).2 2).1 3).2
      75032300095611741602482197255133563788903252114433915072633317750378075907376824191106101884188440146024214).isSome = true := by
  decide +kernel

theorem k3530_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).2 2).2 3).1 2).1
      65593948551460867240209599956813492079264286612438773384599180526647446080929016293008367414408930578415162288609530170861229847).isSome = true := by
  decide +kernel

theorem k3530_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).2 2).2 3).1 2).2
      302351623057078349569251801086508207797400686852831018139769928430489540563900633599914954197236226416538311).isSome = true := by
  decide +kernel

theorem k3530_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).2 2).2 3).2 2).1
      734121066031109164148631835148093404923350372734713571134167767014510907678301968077).isSome = true := by
  decide +kernel

theorem k3530_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).2 2).2 3).2 2).2
      73491664885753324946782265798886569454658993670250543274161219550809884553945452149987515577297077892805).isSome = true := by
  decide +kernel

theorem k3530_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).1 3).1 2).1
      109431993945771925831968762248046694259559864500057566355747860994126444926782907157175788111400724332222769124794511186859875869).isSome = true := by
  decide +kernel

theorem k3530_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).1 3).1 2).2 1).1
      5712332095721837861996582439212733887244980734926539602741512583068224680976442426816360120573073681404973507945845566121336627).isSome = true := by
  decide +kernel

theorem k3530_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).1 3).1 2).2 1).2
      11746639025418301243364808892360938242878791).isSome = true := by
  decide +kernel

theorem k3530_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).1 3).2 2).1
      80218379927592485478529788889802796064887119775841356724680102677307065505739870685989661).isSome = true := by
  decide +kernel

theorem k3530_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).1 3).2 2).2
      228799797140660875687597422430046220372192033978330043325068484933212851307259095693492400089347576024014283549).isSome = true := by
  decide +kernel

theorem k3530_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).2 3).1 1).1 2).1
      65700873889238289752503893297861479983099768714697054372070299043175774866145363974963).isSome = true := by
  decide +kernel

theorem k3530_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).2 3).1 1).1 2).2
      4106331861784858454803392768388633033826910476459530903328957563899378807079944132403).isSome = true := by
  decide +kernel

theorem k3530_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).2 3).1 1).2
      262734647433419453677415037435829047458153231853558933608625431619885901423125925076278).isSome = true := by
  decide +kernel

theorem k3530_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).2 3).2 2).1
      4223847392366462356399990435935311298247799582007906544459710035458271893765051726509639930467151397832613163737373119563361774797).isSome = true := by
  decide +kernel

theorem k3530_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).2 3).2 2).2
      90583118081028318507404261261535672349889110304748067314313097963480167316299188947382751917197370600955189026943101583924227277).isSome = true := by
  decide +kernel

theorem k3530_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).1 3).1 2).1
      5125115683975865872624286877404268629523994868621931919227132499059583853431412381387158215).isSome = true := by
  decide +kernel

theorem k3530_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).1 3).1 2).2
      3563828227786473807712568862195372204266548802104763858153318448147890332128791610949794026149076855440372429).isSome = true := by
  decide +kernel

theorem k3530_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).1 3).2 2).1
      360359876511610356652216907080866874985083880241435871073710965461714467263814346230917567322747328624325).isSome = true := by
  decide +kernel

theorem k3530_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).1 3).2 2).2
      301717116249495845062923193124465596753320429156548847849098737537674901378822440248817205434687771529802445).isSome = true := by
  decide +kernel

theorem k3530_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).2 3).1 2).1
      263117766992405622914145553400195148152179645880152245603117640903831769049812652932326783355009256602681594104020192093264769741).isSome = true := by
  decide +kernel

theorem k3530_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).2 3).1 2).2
      89780329759573910225042909982953705861111750999917042245629453992602069347049851361372834905929206430864579994586079092435213517).isSome = true := by
  decide +kernel

theorem k3530_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).2 3).2 2).1
      65620386745445707851578533519380425523014532419561150457131203742320626241164403741750452905318121405886946386370009504376779461).isSome = true := by
  decide +kernel

theorem k3530_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).2 3).2 2).2
      22329378349067007333837103783382551220719925818023752986315196994240370946073758351042092237480053865913275154854599097128153797).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3530 3531 :=
  (Cover.one (box := dirCellBox) (n := 3530)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3530_0) (.leaf _ k3530_1)) (.split 2 (.leaf _ k3530_2) (.leaf _ k3530_3))) (.split 3 (.split 2 (.leaf _ k3530_4) (.leaf _ k3530_5)) (.split 2 (.leaf _ k3530_6) (.leaf _ k3530_7)))) (.split 2 (.split 3 (.leaf _ k3530_8) (.leaf _ k3530_9)) (.split 3 (.split 2 (.leaf _ k3530_10) (.leaf _ k3530_11)) (.split 2 (.leaf _ k3530_12) (.leaf _ k3530_13))))) (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3530_14) (.split 1 (.leaf _ k3530_15) (.leaf _ k3530_16))) (.split 2 (.leaf _ k3530_17) (.leaf _ k3530_18))) (.split 3 (.split 1 (.split 2 (.leaf _ k3530_19) (.leaf _ k3530_20)) (.leaf _ k3530_21)) (.split 2 (.leaf _ k3530_22) (.leaf _ k3530_23)))) (.split 2 (.split 3 (.split 2 (.leaf _ k3530_24) (.leaf _ k3530_25)) (.split 2 (.leaf _ k3530_26) (.leaf _ k3530_27))) (.split 3 (.split 2 (.leaf _ k3530_28) (.leaf _ k3530_29)) (.split 2 (.leaf _ k3530_30) (.leaf _ k3530_31)))))))

end C4.Cert.Dir104

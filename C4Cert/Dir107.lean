module

public import C4Check

public section

/-! Cells `3558 ≤ n < 3559` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir107

theorem k3558_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).1 3).1 1).1 2).1
      4113067650452470142956395995792570497843836865150234936089835104485429288630201915187).isSome = true := by
  decide +kernel

theorem k3558_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).1 3).1 1).1 2).2
      4122836515196816309359122380687169470519456720239708947799481537943242185847090779955).isSome = true := by
  decide +kernel

theorem k3558_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).1 3).1 1).2
      77610541949536036995813796826451746025977003472022533874067119272370765554521793352230459172187528320423814).isSome = true := by
  decide +kernel

theorem k3558_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).1 3).2 1).1 2).1
      4068745373291720042557721594274988137029514597695409496865752667610758328484545353523).isSome = true := by
  decide +kernel

theorem k3558_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).1 3).2 1).1 2).2
      4074737537923460520422249242190261280470368258438937595512957647841229592553001670451).isSome = true := by
  decide +kernel

theorem k3558_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).1 3).2 1).2
      1419768910625751363565466691452432615143635373950576413265714171671336174823800948876204313627153984353978387327513227058550662).isSome = true := by
  decide +kernel

theorem k3558_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).2 3).1 1).1
      92382059122541664463590124561432514769968788502374380065352299820095385671379422339569641145027331852887645713108999565951323954).isSome = true := by
  decide +kernel

theorem k3558_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).2 3).1 1).2
      1056440838990782969215632358230340774331472306415941701097464735876200976030442509690062).isSome = true := by
  decide +kernel

theorem k3558_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).2 3).2 1).1
      26920777189725710260428424646248706591120921171246706966346578467628281603221063016533496576872998569233904851484529113168045780477680964133930949838).isSome = true := by
  decide +kernel

theorem k3558_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).2 3).2 1).2
      308934880829781712855027912065855168567048008177474681140643291491665187623717139743099454334618284141533062).isSome = true := by
  decide +kernel

theorem k3558_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).1 2).1 1).1
      1060378957590015606165791581775443530555959373346651806548889415085690973893350665147598).isSome = true := by
  decide +kernel

theorem k3558_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).1 2).1 1).2
      4132052311694218216459891093657416303639900808509526454575240766995493904600295872306).isSome = true := by
  decide +kernel

theorem k3558_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).1 2).2 1).1
      4148388773474352157130520965780370977764638340640479006560490632627963828260495808305).isSome = true := by
  decide +kernel

theorem k3558_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).1 2).2 1).2
      56075415888337835505371538958839581409274414171445279643245778738).isSome = true := by
  decide +kernel

theorem k3558_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).2 2).1 1).1
      5725103701897853609063459065614956858444718152138159133242891883826254514787940145166960749660543273719214888043388530219932466).isSome = true := by
  decide +kernel

theorem k3558_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).2 2).1 1).2
      261814439826809786946559471718103943143908866840683122796291063062700322572743478176994).isSome = true := by
  decide +kernel

theorem k3558_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).2 2).2 1).1
      65637620260612612408325428029059708620983471058218135816189332134750163842027159919410).isSome = true := by
  decide +kernel

theorem k3558_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).2 2).2 1).2
      4093385378071021213163427834858127709383821033898696294947807827468833782016419862322).isSome = true := by
  decide +kernel

theorem k3558_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).1 3).1 2).1
      6643776821013692041713161418671661350196516322551619875610215679160591388784068908179674198007279826914259251091581340391251623757379340526080384205).isSome = true := by
  decide +kernel

theorem k3558_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).1 3).1 2).2
      26612022058328826926452891143102023996737026810107859966799460063818234243075119622822581645629461921454423781892365987766852132558809870549905398989).isSome = true := by
  decide +kernel

theorem k3558_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).1 3).2 2).1
      357508846335911270251273479556254707469644543132430000030526468553415603641517303746425978214214185847204904721311897169268948145).isSome = true := by
  decide +kernel

theorem k3558_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).1 3).2 2).2
      22876682058860417406067421200545187942437462747977745115673125168314511452081898167682016210656781799365769056714481361583135349957).isSome = true := by
  decide +kernel

theorem k3558_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).2 3).1 1).1 2).1
      4046159341070903151421752590263754256279726544648138753713632706510636428256070194995).isSome = true := by
  decide +kernel

theorem k3558_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).2 3).1 1).1 2).2
      55018090401816128513250231184631722549142966320083242394180869836).isSome = true := by
  decide +kernel

theorem k3558_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).2 3).1 1).2
      5644132145415018893932376886535150600309647056228405119799165755208487200406284361875734928383797549687439507424438067157276550).isSome = true := by
  decide +kernel

theorem k3558_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).2 3).2 1).1
      4868801148799685590230374767794177528263643572876380037493254933386562477293217478649233478638208415591660338).isSome = true := by
  decide +kernel

theorem k3558_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).2 3).2 1).2
      5608276075163199732369359759081862324754014844404068072322561758327362852310797421715526226871374427097870728384583158084048774).isSome = true := by
  decide +kernel

theorem k3558_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).1 3).1 1).1
      5669705449522794599142343767133862128250554992265989954470632714347060428685913351190556174507582982262647059714470424055503666).isSome = true := by
  decide +kernel

theorem k3558_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).1 3).1 1).2
      76678216143713372923266552695419641992580097345372961541017273173896814324393693536126016874023740313557810).isSome = true := by
  decide +kernel

theorem k3558_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).1 3).2 1).1
      4132593956252995004862912791543872786080909415280788773043498565628564450527235863374642).isSome = true := by
  decide +kernel

theorem k3558_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).1 3).2 1).2
      1032111946533649985156814435603640982103734374754761632045890226965647003780472484764466).isSome = true := by
  decide +kernel

theorem k3558_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).2 3).1 1).1
      76965613848785196352407101304766378032516525111957881298952195748334057454847094311343832306927038073527090).isSome = true := by
  decide +kernel

theorem k3558_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).2 3).1 1).2
      64999424171038669521687480306228611913130893187578292775557192872056678613167811681506).isSome = true := by
  decide +kernel

theorem k3558_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).2 3).2 1).1
      1034934611220014570832434778048679449613118001953910078297503547007131431243955370564402).isSome = true := by
  decide +kernel

theorem k3558_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).2 3).2 1).2
      1033899864394135090474332684189602372582372221163863028410148027131450144271204287093554).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3558 3559 :=
  (Cover.one (box := dirCellBox) (n := 3558)
      (.split 3 (.split 2 (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k3558_0) (.leaf _ k3558_1)) (.leaf _ k3558_2)) (.split 1 (.split 2 (.leaf _ k3558_3) (.leaf _ k3558_4)) (.leaf _ k3558_5))) (.split 3 (.split 1 (.leaf _ k3558_6) (.leaf _ k3558_7)) (.split 1 (.leaf _ k3558_8) (.leaf _ k3558_9)))) (.split 3 (.split 2 (.split 1 (.leaf _ k3558_10) (.leaf _ k3558_11)) (.split 1 (.leaf _ k3558_12) (.leaf _ k3558_13))) (.split 2 (.split 1 (.leaf _ k3558_14) (.leaf _ k3558_15)) (.split 1 (.leaf _ k3558_16) (.leaf _ k3558_17))))) (.split 2 (.split 2 (.split 3 (.split 2 (.leaf _ k3558_18) (.leaf _ k3558_19)) (.split 2 (.leaf _ k3558_20) (.leaf _ k3558_21))) (.split 3 (.split 1 (.split 2 (.leaf _ k3558_22) (.leaf _ k3558_23)) (.leaf _ k3558_24)) (.split 1 (.leaf _ k3558_25) (.leaf _ k3558_26)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3558_27) (.leaf _ k3558_28)) (.split 1 (.leaf _ k3558_29) (.leaf _ k3558_30))) (.split 3 (.split 1 (.leaf _ k3558_31) (.leaf _ k3558_32)) (.split 1 (.leaf _ k3558_33) (.leaf _ k3558_34)))))))

end C4.Cert.Dir107

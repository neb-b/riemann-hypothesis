module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ExistsEpsPeriodTUnit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.TowerSmulZero
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.AtlasOf
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueB'

variable {l : ℕ} [Fact l.Prime]

def βS (hC : B.Compat l) {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (k : Bool) (j : ℕ) :
    Sys.Hom (B.HcSys F κ k j) (MSys (F.pt κ) j) (RingHom.id _) where
  f n := B.β F κ k n j
  comm n x := (hC.red F κ k n.le_succ j x).symm

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem atlas_of {M : Model l K} (h : M.Sm) : ∃ d, Nonempty ((B.schFn M.p).Atlas d) := by
  obtain ⟨hG, hS⟩ := h
  have hP := AdicGeo.proper_p hG
  exact B.P.atlas M.p

variable (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

def bβ (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) :
    ((dat Amp).H a).N j →ₗ[(per l K).A] ((dat Amp).A a).N j :=
  (βS hC (B.schFn M.p) (okToOC l K) false j).lim

def bβ' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) :
    ((dat Amp).H' a).N j →ₗ[(per l K).A] ((dat Amp).A a).N j :=
  (βS hC (B.schFn M.p) (okToOC l K) true j).lim

theorem f_inj (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ x, bβ Amp hC a j x = 0 → (per l K).t ^ n • x = 0 := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun x hx => GlueBL.lim_inj (βS hC (B.schFn M.p) (okToOC l K) false j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 false) x hx⟩

theorem f_inj' (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ x, bβ' Amp hC a j x = 0 → (per l K).t ^ n • x = 0 := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun x hx => GlueBL.lim_inj (βS hC (B.schFn M.p) (okToOC l K) true j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 true) x hx⟩

theorem f_surj' (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ y, ∃ x, bβ' Amp hC a j x = (per l K).t ^ n • y := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun y => GlueBL.lim_surj (βS hC (B.schFn M.p) (okToOC l K) true j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 true) y⟩

theorem f_surj (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ y, ∃ x, (dat Amp).fil a j n x ∧ bβ Amp hC a j x = (per l K).t ^ n • y := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  refine ⟨2 * N, fun y => ?_⟩
  obtain ⟨x, hx, hxy⟩ := GlueBL.lim_surj_fil (βS hC (B.schFn M.p) (okToOC l K) false j) ε.μ u (per l K).t N ht
    (fun n r => B.HcFil (B.schFn M.p) (okToOC l K) false n r j)
    (fun n r x hx => hC.smul_fil (B.schFn M.p) (okToOC l K) false n r j ε.μ (ε.μ_mem false (PAlg.base l) n) x hx)
    (fun n x hx => ((hN (B.schFn M.p) (okToOC l K) ε A n).1 false).1 x hx)
    (fun n y => (hN (B.schFn M.p) (okToOC l K) ε A n).2 y) y
  exact ⟨x, hx, hxy⟩

end GlueB'

end CrystallineSemistableComparison
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.EtaleMapFirstChern
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueE

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem kill_acr (P : PAlg l ⥤ Type) (n : ℕ) (T : El P) (x : (CH.modF (AcrEl P n)).obj T) :
    ((l : Acris l) ^ n) • x = 0 :=
  modF_smul (AcrEl P n) _ (fun T => show algebraMap (Acris l) (((elπ P).obj T).Acr n) ((l : Acris l) ^ n) = 0 by
    rw [map_pow, map_natCast]; exact ((elπ P).obj T).pow_l_acr n) T x

theorem kill_MS (P : PAlg l ⥤ Type) (n j : ℕ) (x : (MSys P j).M n) : ((l : Acris l) ^ n) • x = 0 :=
  tower_smul_zero (fun n => CH.modF (AcrEl P n)) (fun n => redEl P n.le_succ) j n _ (fun T y => kill_acr P n T y) x

variable (e : E.EtFam l K) (he : e.Red)

def eMap (M : Model l K) (j : ℕ) : M.T j →+ (M.MS j).lim where
  toFun v := ⟨fun n => e M n j (v.lev n), fun n => (he M n j _).trans (congrArg (e M n j) (v.2 n))⟩
  map_zero' := Subtype.ext (funext fun n => map_zero (e M n j))
  map_add' v w := Subtype.ext (funext fun n => map_add (e M n j) (v.lev n) (w.lev n))

theorem eMap_lin_lev (M : Model l K) (j : ℕ) (f : ℤ_[l] →+* Acris l) (z : ℤ_[l]) (v : M.T j) (n : ℕ) :
    (eMap e he M j (z • v)).1 n = f z • (eMap e he M j v).1 n :=
  ((congrArg (e M n j) (GlobalTheory.EtC.HtL.smul_eq l n n le_rfl M.spc j 0 z (v.1 n))).trans
    (map_nsmul (e M n j) _ _)).trans (padic_smul f n ((eMap e he M j v).1 n) (kill_MS M.P n j _) z).symm

theorem eMap_lin (M : Model l K) (j : ℕ) (f : ℤ_[l] →+* Acris l) (z : ℤ_[l]) (v : M.T j) :
    eMap e he M j (z • v) = f z • eMap e he M j v :=
  lim_ext fun n => (eMap_lin_lev e he M j f z v n).trans (lim_smul_val _ _ _ n).symm

theorem eMap_act (hq : e.Equi) (M : Model l K) (j : ℕ) (σ : Gal(PadicAlgCl l/K)) (v : M.T j) :
    eMap e he M j (GlobalTheory.EtC.galHl l (PadicAlgCl l) M.q j 0 σ v) = (M.galS j σ).lim (eMap e he M j v) :=
  lim_ext fun n => hq M n j σ (v.lev n)

theorem eMap_phi (hp : e.Phi) (M : Model l K) (j : ℕ) (v : M.T j) :
    (M.phiS j).lim (eMap e he M j v) = eMap e he M j v :=
  lim_ext fun n => hp M n j (v.lev n)

theorem eMap_nat (hn : e.Natu) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (j : ℕ) (v : N.T j) :
    eMap e he M j (Model.pullT u hu j v) = (Model.pullS u hu j).lim (eMap e he N j v) :=
  lim_ext fun n => hn M N u hu n j (v.lev n)

theorem eMap_cup (hc : e.Cup) (M : Model l K) {i j : ℕ} (x : M.T i) (y : M.T j) (z : M.T (i + j)) (h : M.CupT x y z)
    (n : ℕ) : (eMap e he M (i + j) z).1 n = (CH.mulP (AcrEl M.P n)).cup rfl ((eMap e he M i x).1 n) ((eMap e he M j y).1 n) :=
  (congrArg (e M n (i + j)) (h n)).trans (hc M n i j (x.lev n) (y.lev n))

theorem eMap_one (ho : e.One) (M : Model l K) : ∃ v : M.T 0, ∀ n, (eMap e he M 0 v).1 n = CH.oneH (AcrEl M.P n) :=
  (ho M).elim fun v hv => ⟨v, hv⟩

theorem etale_map_first_chern (h1 : e.C1) (M : Model l K) (D : E.LineData M.X) (c : Acris l)
    (hc : c = ACris.periodT (untilt_epsilon (p := l))) :
    ∃ v : M.T 2, E.IsFirstChernClassOfLineBundle M.p (okToOC l K) D (c • eMap e he M 2 v).1 := by
  subst hc
  exact (h1 M D).elim fun v hv => ⟨v, by rw [lim_smul_fun]; exact hv⟩

def emap (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (e : E.EtFam l K) (he : e.Good) : EMap Model.Sm (dat Amp) where
  e {M} _ j := eMap e he.red M j
  lin {M} _ _ j z v := eMap_lin e he.red M j (per l K).z z v
  act {M} _ _ j _ v := eMap_act e he.red he.equi M j _ v
  phi {M} _ _ j v := eMap_phi e he.red he.phi M j v
  nat {_ _ u hu _ _} _ _ _ j v := eMap_nat e he.red he.nat u hu j v
  cup {M} _ _ _ _ x y z h := eMap_cup e he.red he.cup M x y z h
  one {M} _ _ := eMap_one e he.red he.one M
  c1 {M} a _ := etale_map_first_chern e he.red he.c1 M a.1 (per l K).t rfl

end GlueE

theorem glueE : GlueE := fun _ _ _ Amp hE => hE.elim fun e he => ⟨GlueE.emap Amp e he⟩

end CrystallineSemistableComparison
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.FirstChernClassUnique
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueL'

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

theorem ch (hS : ∀ M : Model l K, M.Sm → ∃ D, Amp M D) (M : Model l K) (hM : M.Sm) : Nonempty ((dat Amp).Ch M) :=
  Exists.elim (hS M hM) fun D hD => ⟨(⟨D, hD⟩ : {D : E.LineData M.X // Amp M D})⟩

theorem refine (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (a : (dat Amp).Ch M) (b : (dat Amp).Ch N) :
    ∃ a' : (dat Amp).Ch M, Nonempty ((dat Amp).Mo (𝟙 M.X) (Category.id_comp _) a' a) ∧ Nonempty ((dat Amp).Mo u hu a' b) :=
  ⟨a, Nonempty.intro (PUnit.unit : PUnit.{2}), Nonempty.intro (PUnit.unit : PUnit.{2})⟩

theorem act_smul {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (σ : K.fixingSubgroup) (c : (per l K).A)
    (y : ((dat Amp).A a).N j) : ((dat Amp).A a).act j σ (c • y) = (per l K).σA σ c • ((dat Amp).A a).act j σ y :=
  GlueLim.act_smul M.MS (fun j g => M.galS j (IntermediateField.fixingSubgroupEquiv K g)) j σ c y

theorem phi_smul {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (c : (per l K).A) (y : ((dat Amp).A a).N j) :
    (dat Amp).phiA a j (c • y) = (per l K).φ c • (dat Amp).phiA a j y :=
  GlueLim.hom_smul (M.phiS j) c y

theorem one_uniq {M : Model l K} (a : (dat Amp).Ch M) (x y : ((dat Amp).A a).N 0) :
    ((dat Amp).A a).one x → ((dat Amp).A a).one y → x = y :=
  GlueLim.one_uniq M.MS _ _ _ x y

theorem cup_uniq {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (x : ((dat Amp).A a).N i) (y : ((dat Amp).A a).N j)
    (z z' : ((dat Amp).A a).N (i + j)) : ((dat Amp).A a).cup x y z → ((dat Amp).A a).cup x y z' → z = z' :=
  GlueLim.cup_uniq M.MS _ _ _ x y z z'

theorem bil (M : Model l K) (n i j : ℕ) : ∃ b : (M.MS i).M n →ₗ[Acris l] (M.MS j).M n →ₗ[Acris l] (M.MS (i + j)).M n,
    ∀ x y, b x y = (CH.mulP (AcrEl M.P n)).cup rfl x y :=
  P.cup_bilin (CH.mulP (AcrEl M.P n)) rfl

theorem cup_smul {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (c c' : (per l K).A) (x : ((dat Amp).A a).N i)
    (y : ((dat Amp).A a).N j) (z : ((dat Amp).A a).N (i + j)) :
    ((dat Amp).A a).cup x y z → ((dat Amp).A a).cup (c • x) (c' • y) ((c * c') • z) :=
  GlueLim.cup_smul M.MS _ _ (fun n _ _ x y => (CH.mulP (AcrEl M.P n)).cup rfl x y) (bil M) c c' x y z

theorem first_chern_class_unique (hR : E.RIn l) (hU : E.FirstChernUniqueEtale) (hEt : ∀ M D, Amp M D → Etale D.f) {M : Model l K} (a : (dat Amp).Ch M)
    (x y : ((dat Amp).A a).N 2) : (dat Amp).c1A a x → (dat Amp).c1A a y → x = y := fun hx hy =>
  Subtype.ext (hU l hR (OK l K) M.X M.p (okToOC l K) a.1 (hEt M a.1 a.2) _ _ hx hy)

theorem red_cup (hC : B.CompatH l) (M : Model l K) (k : Bool) (n i j : ℕ) (x : (M.HS k i).M (n + 1)) (y : (M.HS k j).M (n + 1)) :
    (M.HS k (i + j)).r n ((CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) k (n + 1))).cup rfl x y) =
      (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) k n)).cup rfl ((M.HS k i).r n x) ((M.HS k j).r n y) :=
  hC.cup (B.schFn M.p) (okToOC l K) k n.le_succ rfl x y

theorem cup_ex (hC : B.CompatH l) {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (x : ((dat Amp).H a).N i)
    (y : ((dat Amp).H a).N j) : ∃ z, ((dat Amp).H a).cup x y z :=
  GlueLim.cup_ex (M.HS false) _ _ (fun n _ _ x y => (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) false n)).cup rfl x y)
    (red_cup hC M false) x y

end GlueL'

theorem glueL : GlueL := fun _ _ _ Amp hC hR hU hEt hS =>
  { ch := GlueL'.ch Amp hS
    refine := fun M N u hu _ _ a b => GlueL'.refine Amp M N u hu a b
    act_smul := GlueL'.act_smul Amp
    phi_smul := GlueL'.phi_smul Amp
    one_uniq := GlueL'.one_uniq Amp
    cup_uniq := GlueL'.cup_uniq Amp
    cup_smul := GlueL'.cup_smul Amp
    first_chern_class_unique := GlueL'.first_chern_class_unique Amp hR hU hEt
    cup_ex := GlueL'.cup_ex Amp hC }

end CrystallineSemistableComparison
end
end


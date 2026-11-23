module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleDescentOfParity
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0469

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OverAllExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ValDbl

variable {D : D7}

theorem vac_at {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {v : Pl D}
    {f : WO S T → ℂ} (hv : P v) (h : Vac ψ S T LS LT P f) : Vac ψ S T LS LT (· = v) f := by
  have hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hz, rest⟩
    exact ⟨α, hα, fun v' hv' => hz v' (fun e => hv' (by subst e; exact hv)), rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sOp_smul {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (P : Pair k n)
    (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (c : ℂ) (φ₀ : GA D S → ℂ) :
    sOp β P q χ ε (c • φ₀) = c • sOp β P q χ ε φ₀ := by
  have h : formAt β P (c • φ₀) = c • formAt β P φ₀ := by
    funext P₁
    simp only [formAt, map_smul, Pi.smul_apply]
  simp only [sOp, h, map_smul, Pi.smul_apply]

theorem over_keep {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {p : SplitPt D k}
    {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (hstd : IsStdChar D ψ (-1))
    {α : Frame p S m'} {β : Frame p T m} {g f : WO S T → ℂ} {Φ : Matrix m m' k → ℂ}
    (h : Over ψ α β LS LT g Φ f) :
    IsThetaFunO ψ S T f ∧ ∀ v, v ≠ p.v → Vac ψ S T LS LT (· = v) g → Vac ψ S T LS LT (· = v) f := by
  have H := (_root_.GlobalTheory.FinPl.overBasic D k p m m' ψ hstd S T α β LS LT h.1 h.2.1 g h.2.2.1).2.1 Φ f h
  exact ⟨H.1, fun v hv hg => H.2 LS LT (· = v) (fun e => hv e.symm) hg⟩

variable {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type} [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S}
  {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem overAll_nil {f f' : WO S T → ℂ} : OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {i : ι} {l : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: l) f f' ↔ ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' :=
  Iff.rfl

theorem overAll_theta (hstd : IsStdChar D ψ (-1)) (l : List ι) :
    ∀ f f', OverAll ψ α β LS LT Ψ l f f' → IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' := by
  induction l with
  | nil => intro f f' h hf; rw [overAll_nil.1 h]; exact hf
  | cons i l _ =>
    intro f f' h _
    obtain ⟨g, -, hf'⟩ := overAll_cons.1 h
    exact (over_keep hstd hf').1

theorem overAll_vac (hstd : IsStdChar D ψ (-1)) (hinj : Function.Injective fun i => (p i).v) (l : List ι) :
    ∀ f f', OverAll ψ α β LS LT Ψ l f f' → ∀ j, j ∉ l →
      Vac ψ S T LS LT (· = (p j).v) f → Vac ψ S T LS LT (· = (p j).v) f' := by
  induction l with
  | nil => intro f f' h j _ hf; rw [overAll_nil.1 h]; exact hf
  | cons i l ih =>
    intro f f' h j hj hf
    obtain ⟨g, hg, hf'⟩ := overAll_cons.1 h
    have hji : j ≠ i := fun e => hj (by simp [e])
    have hjl : j ∉ l := fun h' => hj (by simp [h'])
    exact (over_keep hstd hf').2 _ (fun e => hji (hinj e)) (ih f g hg j hjl hf)

theorem overAll_last (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (l : List ι) : l.Nodup → ∀ f f', (∀ j, Vac ψ S T LS LT (· = (p j).v) f) → OverAll ψ α β LS LT Ψ l f f' →
      ∀ i ∈ l, ∃ g, Over ψ (α i) (β i) LS LT g (Ψ i) f' ∧ ∀ j, (j = i ∨ j ∉ l) → Vac ψ S T LS LT (· = (p j).v) g := by
  induction l with
  | nil => intro _ _ _ _ _ i hi; simp at hi
  | cons j l ih =>
    intro hl f f' hf h i hi
    rw [List.nodup_cons] at hl
    obtain ⟨g₀, hg₀, hf'⟩ := overAll_cons.1 h
    by_cases hij : i = j
    · subst hij
      refine ⟨g₀, hf', fun j' hj' => ?_⟩
      have hj'l : j' ∉ l := by
        rcases hj' with rfl | hj'
        · exact hl.1
        · exact fun h' => hj' (List.mem_cons_of_mem _ h')
      exact overAll_vac hstd hinj l f g₀ hg₀ j' hj'l (hf j')
    · have hil : i ∈ l := by simpa [hij] using hi
      obtain ⟨g₁, hg₁, hv₁⟩ := ih hl.2 f g₀ hf hg₀ i hil
      have hjv : Vac ψ S T LS LT (· = (p j).v) g₁ := hv₁ j (Or.inr hl.1)
      obtain ⟨g', hg'1, hg'2⟩ := _root_.GlobalTheory.FinPl.overSwap D k (p i) (p j) n n' n n' ψ hstd (hunit i) (hunit j)
        (fun e => hij (hinj e)) S T (α i) (β i) (α j) (β j) LS LT g₁ g₀ f' (Ψ i) (Ψ j) hjv hg₁ hf'
      refine ⟨g', hg'2, fun j' hj' => ?_⟩
      have hne : j' ≠ j := by
        rcases hj' with rfl | hj'
        · exact hij
        · exact fun e => hj' (by simp [e])
      have hj'' : j' = i ∨ j' ∉ l := by
        rcases hj' with rfl | hj'
        · exact Or.inl rfl
        · exact Or.inr fun h' => hj' (List.mem_cons_of_mem _ h')
      exact (over_keep hstd hg'1).2 _ (fun e => hne (hinj e)) (hv₁ j' hj'')

end Local

theorem contAut_hand0 {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) {φ : GA D B.A → ℂ}
    {Ξ₁ : WO B.V₀ J.W₀ → ℂ} {Ξ₂ : WO J.W₀ B'.V₀ → ℂ} (hφ : IsContAut B.A φ) (h₁ : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁)
    (h₂ : IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂) : IsContAut B'.A (hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂) :=
  _root_.GlobalTheory.handFBLaw D ψ σ J B' s₂ vL _ Ξ₂ (_root_.GlobalTheory.UnfLink.link D ψ (σ + 1) B J s₁ B'.L B'.ζ B'.line l φ Ξ₁ hφ h₁).1 h₂

end GlobalTheory.FinPl.ValDbl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffBessel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepSuppSecond

variable {D : D7}

theorem mem_congGrp {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem grpAt_inter {V : HSp D} {P P' R : Pl D → Prop} (h : ∀ p, P p → P' p → R p) {g : GA D V}
    (hg : g ∈ grpAt V P) (hg' : g ∈ grpAt V P') : g ∈ grpAt V R := by
  rw [grpAt, mem_congGrp] at hg hg' ⊢
  intro i j
  have h1 := hg i j
  have h2 := hg' i j
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h1 h2 ⊢
  refine ⟨h1.1, fun u => ?_⟩
  by_cases hp : P u.1
  · exact h2.2 ⟨u.1, fun hp' => u.2 (h _ hp hp')⟩
  · exact h1.2 ⟨u.1, hp⟩

theorem grpAt_mono {V : HSp D} {P R : Pl D → Prop} (h : ∀ p, P p → R p) {g : GA D V}
    (hg : g ∈ grpAt V P) : g ∈ grpAt V R := grpAt_inter (fun p hp _ => h p hp) hg hg

theorem grpAt_off {V : HSp D} {P R : Pl D → Prop} (h : ∀ p, P p → ¬ R p) {g : GA D V}
    (hg : g ∈ grpAt V P) : g ∈ grpOff V R := by
  rw [grpAt, mem_congGrp] at hg
  rw [grpOff, mem_congGrp]
  intro i j
  have h1 := hg i j
  simp only [idAt, idOff, Submodule.mem_inf, Submodule.mem_iInf] at h1 ⊢
  exact fun u => h1.2 ⟨u.1, fun hp => h _ hp u.2⟩

theorem grpAt_fin {V : HSp D} {P : Pl D → Prop} {g : GA D V} (hg : g ∈ grpAt V P) : g ∈ GfC V :=
  (_root_.GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.1 (grpAt_mono (fun p _ => Finset.notMem_empty p) hg)

theorem split_two {V : HSp D} (G Q : Finset (Pl D)) {x : GA D V} (hx : x ∈ GfC V)
    (hx' : x ∈ grpOff V fun p => p ∉ G ∧ p ∉ Q) :
    ∃ y ∈ grpAt V (· ∈ Q), ∃ z ∈ grpAt V (· ∈ G), x = y * z := by
  obtain ⟨-, -, hQ, -, -, ⟨e, he⟩, -, hinf, -⟩ := _root_.GlobalTheory.FinPl.SetCut.grp_split D V Q
  obtain ⟨p, hp⟩ := e.surjective ⟨x, hx⟩
  have hxe : x = p.1.1 * p.2.1 := by rw [← he p, hp]
  refine ⟨p.1.1, p.1.2, p.2.1, ?_, hxe⟩
  have h1 : p.2.1 ∈ grpAt V fun q => ¬ (q ∉ G ∧ q ∉ Q) := by
    rw [← hinf]
    have : p.2.1 = p.1.1⁻¹ * x := by rw [hxe]; group
    rw [this]
    exact Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem (hQ p.1.2)) hx, mul_mem (inv_mem (grpAt_off (fun q hq hq' => hq'.2 hq) p.1.2)) hx'⟩
  exact grpAt_inter (fun q h h' => by_contra fun hG => h ⟨hG, h'⟩) h1 p.2.2

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f := by
  have hm : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) P' := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun p hp => hv p fun hq => hp (h p hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hm hu), fun e he u hu hh => hf.2.2 e he u (hm hu) hh⟩

theorem moved_data {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {LS : Lat S} {LT : Lat T} {G Q : Finset (Pl D)} (hd : Disjoint Q G)
    {eG eQ : WO S T →₀ ℂ} (hG : CombAt (· ∈ G) eG) (hQ : CombAt (· ∈ Q) eQ) {Ψ : WO S T → ℂ}
    (hΨ : Vac ψ S T LS LT (fun _ => True) Ψ) {a : GA D S} {b : GA D T} (ha : a ∈ grpAt S (· ∈ Q)) (hb : b ∈ grpAt T (· ∈ Q)) :
    Vac ψ S T LS LT (fun p => p ∉ G ∧ p ∉ Q) (om (a, b) (comb ψ S T eG (comb ψ S T eQ Ψ))) ∧
      ∃ Ψ', Vac ψ S T LS LT (· ∈ G) Ψ' ∧ om (a, b) (comb ψ S T eG (comb ψ S T eQ Ψ)) = comb ψ S T eG Ψ' := by
  have hI := GlobalTheory.DisjComb.main D ψ hW.std S T
  have hQG : ∀ p, p ∈ Q → ¬ p ∈ G := fun p hp => Finset.disjoint_left.mp hd hp
  have hQo : ∀ p, p ∈ Q → ¬ (p ∉ G ∧ p ∉ Q) := fun p hp h => h.2 hp
  have hGo : ∀ p, p ∈ G → ¬ (p ∉ G ∧ p ∉ Q) := fun p hp h => h.1 hp
  have h1 : Vac ψ S T LS LT (· ∈ G) (comb ψ S T eQ Ψ) :=
    ((hI (· ∈ Q) (· ∈ G) hQG).2.1 eQ hQ).2 _ _ _ (vac_mono (fun _ _ => trivial) hΨ)
  refine ⟨GlobalTheory.OffPlaceWeil.vac_off hW ?_ (grpAt_off hQo ha) (grpAt_off hQo hb), om (a, b) (comb ψ S T eQ Ψ),
    GlobalTheory.OffPlaceWeil.vac_off hW h1 (grpAt_off hQG ha) (grpAt_off hQG hb), ?_⟩
  · exact ((hI (· ∈ G) _ hGo).2.1 eG hG).2 _ _ _
      (((hI (· ∈ Q) _ hQo).2.1 eQ hQ).2 _ _ _ (vac_mono (fun _ _ => trivial) hΨ))
  · exact (hI (· ∈ G) _ hGo).2.2.1 χS χT om hW eG hG a (grpAt_off hQG ha) b (grpAt_off hQG hb) _ h1.1

theorem om_mul {S T : HSp D} (om : Om S T) (a a' : GA D S) (b b' : GA D T) (f : WO S T → ℂ) :
    om (a * a', b * b') f = om (a, b) (om (a', b') f) := by
  rw [← Prod.mk_mul_mk, map_mul]
  rfl

theorem integ_support : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∀ q₂ ∈ GfC (c.V (j + 1 + 1)), integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1 + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1 + 1)) (v.N (j + 1 + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1 + 1), q₂ = r * y * (κ * k) := by
  intro D c v t w hc hv ht hF hW hO hGs _ hC hFl j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f _ q₁ hq₁ q₂ hq₂ hne
  obtain ⟨α, -, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨g, hg, hαg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
  have hgQ := (hF.e j α).2 g hg
  have e₁ := (ht.sBF j (σ + 1) h).1
  have e₂ := (ht.sFB j σ h).1
  have W₁ : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) _ _ (t.om j) := e₁ ▸ (t.sBF j (σ + 1) h).weil
  have W₂ : IsWeilDatumO c.ψ (c.V (j + 1)) (c.V (j + 1 + 1)) _ _ (t.om (j + 1)) := e₂ ▸ (t.sFB j σ h).weil
  set Φ₁ := comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁) with hΦ₁
  set Φ₂ := comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) with hΦ₂
  have hH : handFB (t.sFB j σ h) (c.vL j σ h) (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α)
      (flatBF (t.sBF j (σ + 1) h) (t.om j (g, q₁) Φ₁))) (flatFB (t.sFB j σ h) (t.om (j + 1) (q₁, q₂) Φ₂)) ≠ 0 := by
    intro h0
    apply hαg
    have hp := (GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (φ α)).2.2
      0 1 0 (rTrans q₂ f)
    rw [zero_smul, one_smul, zero_mul, zero_mul] at hp
    rw [Chain.hand, e₁, e₂]
    erw [h0, hp]
    exact mul_zero _
  obtain ⟨V₁, Ψ₁', V₁', E₁⟩ := moved_data W₁ hF.disjG (hv.atG j).1 (hF.atQ j).1 h₁ hgQ hq₁
  obtain ⟨V₂, -⟩ := moved_data W₂ hF.disjG (hv.atG (j + 1)).1 (hF.atQ (j + 1)).1 h₂ hq₁ (one_mem _)
  obtain ⟨-, hfix, -, hbig⟩ := hO j σ h _ _ V₁ V₂
  obtain ⟨r, hr, hrP, y, hy, κ, hκ, hq⟩ := hbig (φ α) (hφ α) q₂ (by
    rw [Chain.hand, e₁, e₂]
    erw [← om_mul, ← om_mul]
    simp only [one_mul, mul_one]
    exact hH)
  have hyf : y ∈ GfC (c.V (j + 1 + 1)) := by
    have : y = r⁻¹ * q₂ * κ⁻¹ := by rw [hq]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (grpAt_fin hrP)) hq₂) (inv_mem (grpAt_fin hκ.1))
  obtain ⟨yQ, hyQ, z, hz, rfl⟩ := split_two v.gP w.Q hyf hy
  have comm := (_root_.GlobalTheory.FinPl.SetCut.grp_split D (c.V (j + 1 + 1)) v.gP).2.2.2.2.1
  have hQG : ∀ p, p ∈ w.Q → p ∉ v.gP := fun p hp => Finset.disjoint_left.mp hF.disjG hp
  have hyQ' := grpAt_mono hQG hyQ
  have hκ' : κ ∈ grpAt _ (· ∉ v.gP) := grpAt_mono (fun p hp => hp.1) hκ.1
  obtain ⟨-, Ψ₂', V₂', E₂⟩ := moved_data W₂ hF.disjG (hv.atG (j + 1)).1 (hF.atQ (j + 1)).1 h₂ hq₁ hyQ
  have hΦ : t.om (j + 1) (q₁, q₂) Φ₂ =
      t.om (j + 1) (1, r) (t.om (j + 1) (1, z) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂')) := by
    have s1 : t.om (j + 1) (q₁, q₂) Φ₂ =
        t.om (j + 1) (1, r * (yQ * z)) (t.om (j + 1) (1, κ) (t.om (j + 1) (q₁, 1) Φ₂)) := by
      rw [← om_mul, ← om_mul, hq]
      simp only [one_mul, mul_one]
    rw [s1, hfix κ hκ, ← E₂, ← om_mul, ← om_mul, ← om_mul, ← comm z hz yQ hyQ']
    simp only [one_mul, mul_one, mul_assoc]
  have T₁ : IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (v.eG j) Ψ₁') := E₁ ▸ V₁.1
  have T₂ : IsThetaFunO c.ψ _ _ (t.om (j + 1) (1, z) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂')) := by
    refine W₂.om_pres _ _ ?_
    rw [← E₂]
    exact (moved_data W₂ hF.disjG (hv.atG (j + 1)).1 (hF.atQ (j + 1)).1 h₂ hq₁ hyQ).1.1
  have hR := (_root_.GlobalTheory.FlatRInv.vanish_invariant D c.ψ (offP v w)).2 σ _ _ (t.sFB j σ h) (c.vL j σ h)
    (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α) (flatBF (t.sBF j (σ + 1) h) (comb c.ψ _ _ (v.eG j) Ψ₁'))) _ T₂ r hr hrP
  rw [e₂] at hR
  rw [hΦ, E₁] at hH
  have hH' := fun h0 => hH (hR.2 h0)
  have hctr : c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (v.eG j) Ψ₁')
      (t.om (j + 1) (1, z) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂')) ≠ 0 := by
    intro h0
    apply hH'
    obtain ⟨χA, χA', χz, omz, omz', a1, a2, a3, a4, a5, a6⟩ := hW.mid j σ h
    have hth := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D hFl c.ψ
    have hcl := (hC c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) χA χA' χz _ omz _ omz'
      a1 a2 a3 a4 a5 a6 (φ α) _ _ (hv.ram j _ (hφ α)).1 (hth.1 _ _ _ (t.sBF j (σ + 1) h) _ T₁)
      (hth.2 _ _ _ (t.sFB j σ h) _ T₂)).2.2
    funext h₂
    rw [hcl h₂]
    unfold Comm.ctr at h0
    erw [h0]
    have z1 : ∀ p vv, t.kom j p (fun u => (0 : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) u vv) 0 = 0 :=
      fun p vv => congrFun (map_zero (t.kom j p)) 0
    have z2 : ∀ p p', t.kom (j + 1) p' (fun vv => t.kom j p
        (fun u => (0 : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) u vv) 0) 0 = 0 := by
      intro p p'
      rw [show (fun vv => t.kom j p
        (fun u => (0 : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) u vv) 0) = 0 from funext (z1 p)]
      exact congrFun (map_zero (t.kom (j + 1) p')) 0
    refine (integral_congr_ae (g := fun _ => 0) (Filter.Eventually.of_forall fun h₁ => ?_)).trans (integral_zero _ _)
    refine (integral_congr_ae (g := fun _ => 0) (Filter.Eventually.of_forall fun h₀ => ?_)).trans (integral_zero _ _)
    exact mul_eq_zero_of_right _ (z2 _ _)
  obtain ⟨r', hr', hr'G, k, hk, hzk⟩ := (hGs j σ h Ψ₁' Ψ₂' V₁' V₂').2 z hz hctr
  have hkG := (hv.JG (j + 1 + 1) (by omega)).1 hk
  refine ⟨r * r', mul_mem hr hr', mul_mem (grpAt_fin hrP) (grpAt_fin hr'G), yQ, hyQ, κ, hκ, k, hk, ?_⟩
  rw [hq, hzk, ← comm k hkG κ hκ', mul_assoc r r' yQ, comm r' hr'G yQ hyQ']
  simp only [mul_assoc]

end GlobalTheory.DStepSuppSecond

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceFinitelyManyCells
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinOneAt


set_option maxHeartbeats 4000000 in
theorem core {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (hψ : IsStdChar D c.ψ (-1)) (hv : v.Is) (ht : t.Is)
    {χ : ℕ → (AE D)ˣ →* Circle} (Q' : QAt v χ) (χz : (AE D)ˣ →* Circle) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (V₁ : (t.sBF j (σ + 1) h).χV = χ j * χz) (W₁ : (t.sBF j (σ + 1) h).χW = χ j)
    (V₂ : (t.sFB j σ h).χV = χ (j + 1)) (W₂ : (t.sFB j σ h).χW = χ (j + 1) * χz)
    (ka : IsWeilDatumO c.ψ _ _ (χ j) (χ j) (t.kom j)) (kb : IsWeilDatumO c.ψ _ _ (χ (j + 1)) (χ (j + 1)) (t.kom (j + 1)))
    (a : GL (Q'.X j ⊕ Fin (2 * σ + 2 + 1)) Q'.k) :
    ∃ T : Finset (GL (Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) Q'.k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Q'.q.v) f₁ →
      ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = Q'.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = Q'.q.v), ∀ x,
        flatBF (t.sBF j (σ + 1) h) (t.om j (g * Q'.gl j (2 * σ + 2 + 1) (by have := Q'.hs; omega) a,
          h₁ * Q'.gl (j + 1) (2 * σ + 2) (by have := Q'.hs; omega) x) (comb c.ψ _ _ (Q'.eL j) f₁)) ≠ 0 →
        ∃ τ ∈ T, ∃ r, Q'.gl (j + 1) (2 * σ + 2) (by have := Q'.hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧
          ∃ κ ∈ (Q'.T.lev (j + 1) (2 * σ + 2) (by have := Q'.hs; omega)).J, x = r * τ * κ := by
  classical
  haveI := Q'.unitVol.1
  have e0 : j + (2 * σ + 2 + 1) = Q'.s + 1 := by have := Q'.hs; omega
  have e1 : j + 1 + (2 * σ + 2) = Q'.s + 1 := by have := Q'.hs; omega
  have e2 : j + 1 + 1 + (2 * σ + 1) = Q'.s + 1 := by have := Q'.hs; omega
  have e01 : j + (2 * σ + 2) = Q'.s := by have := Q'.hs; omega
  have e12 : j + 1 + (2 * σ + 1) = Q'.s := by have := Q'.hs; omega
  let S : Dbl2 c.ψ σ :=
    { B := c.B j (σ + 1) h, J := c.J j (σ + 1) h, B' := c.B (j + 1 + 1) σ (idx_step h),
      s₁ := t.sBF j (σ + 1) h, s₂ := t.sFB j σ h, l := c.lnk j σ h, vL := c.vL j σ h,
      χ₁ := χ j, χ₂ := χ (j + 1), χz := χz, oma := t.kom j, omb := t.kom (j + 1),
      V₁ := V₁, W₁ := W₁, V₂ := V₂, W₂ := W₂, weila := ka, weilb := kb }
  let Fd : Dbl (ofSplit Q'.q) S.B S.J S.B' (Q'.X j) (Q'.X (j + 1)) (Q'.X (j + 1 + 1)) (2 * σ) :=
    { s := Q'.sc j, s_ne := Q'.sc_ne j, F₀ := Q'.FX j (by omega), F₁ := Q'.FX (j + 1) (by omega),
      F₂ := Q'.FX (j + 1 + 1) (by omega), G₀ := Q'.FY j _ e0, G₁ := Q'.FY (j + 1) _ e1, G₂ := Q'.FY (j + 1 + 1) _ e2,
      bes := Q'.bes j (σ + 1) h _ e0, jac := Q'.jac j (σ + 1) h _ e1,
      bes' := by rw [← Q'.sc_step j]; exact Q'.bes (j + 1 + 1) σ (idx_step h) _ e2 }
  have reg1 := (Q'.reg.2.2 (j + 1) _ e1)
  have reg2 := (Q'.reg.2.2 (j + 1 + 1) _ e2)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, A₁, A₂, cov₁, cov₂, d₁, d₂, ent₁, ent₂, e₀, e₂, one₀, one₂, m₁, m₂, haar₁, haar₂,
      vol₁, vol₂, -, -, -⟩ :=
    GlobalTheory.QPl.Inhab.exists_qstep hψ S Q'.ν Q'.unitVol Q'.q Q'.ψk Q'.char Q'.cond (Q'.X j) (Q'.X (j + 1)) (Q'.X (j + 1 + 1))
      (2 * σ) Fd (Q'.T.mu (j + 1)) (Q'.T.mu (j + 1 + 1)) (Q'.mu j (by omega)).1 (Q'.mu (j + 1) (by omega)).1
      (Q'.mu j (by omega)).2 (Q'.mu (j + 1) (by omega)).2 (Q'.T.lev j _ e0) (Q'.T.lev (j + 1) _ e1) (Q'.T.lev (j + 1 + 1) _ e2)
      (Q'.reg.2.2 j _ e0).1 ⟨reg1.1, reg1.2.1⟩ ⟨reg2.1, reg2.2.1⟩ (Q'.le _ _ e1) (Q'.le _ _ e2)
      ⟨Q'.T.Phi j _ e01, Q'.reg.1 _ _ e01⟩ ⟨Q'.T.Phi (j + 1) _ e12, Q'.reg.1 _ _ e12⟩ (Q'.laws.1 j _ e01) (Q'.laws.1 (j + 1) _ e12)
      a 1 1
  let Q : QStep S :=
    { k := Q'.k, ν := Q'.ν, unitVol := Q'.unitVol, q := Q'.q, ψk := Q'.ψk, char := Q'.char, cond := Q'.cond,
      n₀ := Q'.X j, n₁ := Q'.X (j + 1), n₂ := Q'.X (j + 1 + 1), c := 2 * σ, F := Fd,
      gl₀ := Q'.gl j _ e0, gl₁ := Q'.gl (j + 1) _ e1, gl₂ := Q'.gl (j + 1 + 1) _ e2,
      loc₀ := Q'.gl_loc j _ e0, loc₁ := Q'.gl_loc (j + 1) _ e1, loc₂ := Q'.gl_loc (j + 1 + 1) _ e2,
      μ₁ := Q'.T.mu (j + 1), μ₂ := Q'.T.mu (j + 1 + 1), comp₁ := (Q'.mu j (by omega)).1, comp₂ := (Q'.mu (j + 1) (by omega)).1,
      open₁ := (Q'.mu j (by omega)).2, open₂ := (Q'.mu (j + 1) (by omega)).2,
      L₀ := Q'.T.lev j _ e0, L₁ := Q'.T.lev (j + 1) _ e1, L₂ := Q'.T.lev (j + 1 + 1) _ e2,
      co₁ := ⟨reg1.1, reg1.2.1⟩, co₂ := ⟨reg2.1, reg2.2.1⟩, le₁ := Q'.le _ _ e1, le₂ := Q'.le _ _ e2,
      Φ₁ := ⟨Q'.T.Phi j _ e01, Q'.reg.1 _ _ e01⟩, Φ₂ := ⟨Q'.T.Phi (j + 1) _ e12, Q'.reg.1 _ _ e12⟩,
      ty₁ := Q'.laws.1 j _ e01, ty₂ := Q'.laws.1 (j + 1) _ e12,
      D₁ := Q'.eL j, D₂ := Q'.eL (j + 1), dat₁ := Q'.eL_at j _ e01, dat₂ := Q'.eL_at (j + 1) _ e12,
      α := a, A₁ := A₁, A₂ := A₂, cov₁ := cov₁, cov₂ := cov₂, d₁ := d₁, d₂ := d₂, ent₁ := ent₁, ent₂ := ent₂,
      e₀ := e₀, e₂ := e₂, one₀ := one₀, one₂ := one₂, m₁ := m₁, m₂ := m₂, haar₁ := haar₁, haar₂ := haar₂,
      vol₁ := vol₁, vol₂ := vol₂ }
  obtain ⟨T₁, hT₁, -⟩ := _root_.GlobalTheory.QPl.FinOneProof.finOne D c.ψ hψ σ S Q a
  refine ⟨T₁, fun f₁ hf₁ g hg h₁ hh₁ x hx => ?_⟩
  obtain ⟨Tm, hTm, hTmO⟩ := (GlobalTheory.LocMod.indicator_vac D Q'.k Q'.q Q'.unit (Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) (Q'.X j ⊕ Fin (2 * σ + 2 + 1))
    (c.V j) (c.V (j + 1)) (Q'.FY j _ e0) (Q'.FY (j + 1) _ e1) c.ψ Q'.ψk hψ Q'.char Q'.cond (v.N j) (v.N (j + 1))
    (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Q'.latY j _ e0) (Q'.latY (j + 1) _ e1)).2 f₁ hf₁
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Q'.k) (Y := Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) (Y' := Q'.X j ⊕ Fin (2 * σ + 2 + 1))
  obtain ⟨f₀, f₂, -, -, -, -, hv2⟩ := GlobalTheory.QPl.Inhab.exists_vac hψ (ι := Unit) (fun _ => Q) (fun _ _ _ => rfl)
  have hvac : Q.Vac f₁ f₂ := ⟨⟨Tm, O, hTm, hO, hTmO O hO⟩, (hv2 ()).2⟩
  have hom := (ht.sBF j (σ + 1) h).1
  obtain ⟨τ, hτ, r, hr, κ, hκ, hx'⟩ := hT₁ f₁ f₂ hvac g hg h₁ hh₁ x (by
    change flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om _ _) ≠ 0
    rw [hom]; exact hx)
  exact ⟨τ, hτ, r, hr, κ, hκ, hx'⟩

theorem finOne_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ ((F.Q i).eL j) f₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  intro D c v t w F hc ht hv _ hP j σ h i a
  obtain ⟨χz, V₁, W₁, V₂, W₂⟩ := hP.mid j σ h
  exact core hc.std hv ht (F.Q i) χz j σ h V₁ W₁ V₂ W₂ (hP.kom j (by omega)) (hP.kom (j + 1) (by omega)) a

end GlobalTheory.QFinOneAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairStabiliserMemChartLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.StabLev

theorem stab_mem_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → (β j i).gl g ∈ A.U j b := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hStd j hj b i g hg
  rw [hA.U j hj b]
  refine ⟨_root_.GlobalTheory.FrameGfC.gl_mem_GfC _ _ _ _ _ _ _, ?_⟩
  obtain ⟨x, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl ((β j i).gl g)
  have hmem : x.1 ∈ (A.K j hj b).lev.U := by
    rw [(A.K j hj b).lev.U_eq]
    refine ⟨x.2, fun v => ?_⟩
    by_cases hv : v = (p i).v
    · subst hv
      have hT := _root_.GlobalTheory.AdForm.stdT_levelPrime_mem_v I hOk hPins l Z u k ι p β Q L hStd i
      exact GlobalTheory.T.splitPlace_component_keeps_level_functional I hOk hPins l Z u a Ch A hA k ι p β Q L hStd j hj b i g hg x hx hT
        (GlobalTheory.T.splitPlace_component_mem_baseLattice_level_of_fixes_pair I hOk hPins l Z u a Ch A hA k ι p β Q L hStd j hj b i g hg x hx)
    · rw [GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one _ _ _ _ _ _ g _ (rankN (I.rec7 l Z) j hj) x.1 hx v hv]
      exact Subgroup.one_mem _
  exact ⟨⟨x.1, hmem⟩, hx⟩

end GlobalTheory.AdForm.StabLev

end
end


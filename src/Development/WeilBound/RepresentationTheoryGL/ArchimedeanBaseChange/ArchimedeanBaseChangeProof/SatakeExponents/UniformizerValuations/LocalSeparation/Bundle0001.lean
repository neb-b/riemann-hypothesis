module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.LocalL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PPairSat
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

section Gen

variable {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]

theorem heckeVec_pairProd (ρ : Representation ℂ (G₁ × G₂) V) {K₁ : Subgroup G₁} {K₂ : Subgroup G₂}
    (hK₁ : IsCommensurated K₁) (hK₂ : IsCommensurated K₂) {h₁ : G₁ → ℂ} {h₂ : G₂ → ℂ}
    (hh₁ : h₁ ∈ Hecke ℂ K₁) (hh₂ : h₂ ∈ Hecke ℂ K₂) {x : V} (hx : x ∈ fixed ρ (K₁.prod K₂)) :
    heckeVec ρ (K₁.prod K₂) (fun g => h₁ g.1 * h₂ g.2) x =
      heckeVec (ρ.comp (MonoidHom.inl G₁ G₂)) K₁ h₁ (heckeVec (ρ.comp (MonoidHom.inr G₁ G₂)) K₂ h₂ x) := by
  classical
  let e : (G₁ × G₂) ⧸ K₁.prod K₂ ≃ (G₁ ⧸ K₁) × (G₂ ⧸ K₂) :=
    { toFun := fun c => ((c.out.1 : G₁ ⧸ K₁), (c.out.2 : G₂ ⧸ K₂))
      invFun := fun p => (((p.1.out, p.2.out) : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂)
      left_inv := fun c => by
        conv_rhs => rw [← c.out_eq']
        exact QuotientGroup.eq.2 (Subgroup.mem_prod.2
          ⟨QuotientGroup.eq.1 (QuotientGroup.out_eq' _), QuotientGroup.eq.1 (QuotientGroup.out_eq' _)⟩)
      right_inv := fun p => by
        obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K₁.prod K₂) ((p.1.out, p.2.out) : G₁ × G₂)
        simp only [hk, Prod.fst_mul, Prod.snd_mul]
        rw [QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_prod.1 k.2).1,
          QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_prod.1 k.2).2, QuotientGroup.out_eq', QuotientGroup.out_eq'] }
  have hbi : IsBiInv (K₁.prod K₂) (fun g : G₁ × G₂ => h₁ g.1 * h₂ g.2) := fun a b g => by
    have e1 := hh₁.1 ⟨_, (Subgroup.mem_prod.1 a.2).1⟩ ⟨_, (Subgroup.mem_prod.1 b.2).1⟩ g.1
    have e2 := hh₂.1 ⟨_, (Subgroup.mem_prod.1 a.2).2⟩ ⟨_, (Subgroup.mem_prod.1 b.2).2⟩ g.2
    exact congrArg₂ (· * ·) e1 e2
  have hf1 := Formalism.UG.P.finite_support_cosets hK₁ hh₁.2
  have hf2 := Formalism.UG.P.finite_support_cosets hK₂ hh₂.2
  let F : (G₁ ⧸ K₁) × (G₂ ⧸ K₂) → V := fun p => (h₁ p.1.out * h₂ p.2.out) • ρ (p.1.out, p.2.out) x
  have hF : Function.HasFiniteSupport F := by
    refine (hf1.prod hf2).subset fun p hp => ⟨fun h0 => hp ?_, fun h0 => hp ?_⟩
    · simp [F, h0]
    · simp [F, h0]
  rw [heckeVec_eq_of_section hbi hx (fun c => ((e c).1.out, (e c).2.out)) (fun c => e.left_inv c)]
  rw [show (∑ᶠ c, (fun g : G₁ × G₂ => h₁ g.1 * h₂ g.2) ((e c).1.out, (e c).2.out) •
      ρ ((e c).1.out, (e c).2.out) x) = ∑ᶠ c, F (e c) from rfl, finsum_comp_equiv e, finsum_curry F hF]
  simp only [heckeVec]
  refine finsum_congr fun c₁ => ?_
  have hm := ((h₁ c₁.out • (ρ.comp (MonoidHom.inl G₁ G₂)) c₁.out : V →ₗ[ℂ] V).toAddMonoidHom.map_finsum
    (finite_heckeVec hK₂ hh₂ (ρ.comp (MonoidHom.inr G₁ G₂)) x))
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply] at hm
  rw [hm]
  refine finsum_congr fun c₂ => ?_
  simp only [F, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, map_smul, smul_smul]
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem heckeVec_smul_pair (ρ : Representation ℂ G₁ V) {K : Subgroup G₁} (hK : IsCommensurated K) {h : G₁ → ℂ}
    (hh : h ∈ Hecke ℂ K) (c : ℂ) (x : V) : heckeVec ρ K h (c • x) = c • heckeVec ρ K h x := by
  have := map_heckeVec (ρ := ρ) hK hh (c • LinearMap.id) (ρ' := ρ) (fun g y => by simp) x
  simpa using this.symm

theorem heckeVec_zero_pair (ρ : Representation ℂ G₁ V) (K : Subgroup G₁) (h : G₁ → ℂ) : heckeVec ρ K h 0 = 0 := by
  simp [heckeVec]

end Gen

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSlice₁ {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {G : H E a b → ℂ}
    (hG : G ∈ pairSpace U₁ U₂) (y : GA E b) : ∃ φ ∈ U₁, ∀ x, φ.1 x = G (x, y) := by
  induction hG using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    exact ⟨φ₂.1 y • φ₁, U₁.smul_mem _ h₁, fun x => by simp [mul_comm]⟩
  | zero => exact ⟨0, U₁.zero_mem, fun x => rfl⟩
  | add F F' _ _ hF hF' =>
    obtain ⟨φ, hφ, e⟩ := hF
    obtain ⟨φ', hφ', e'⟩ := hF'
    exact ⟨φ + φ', U₁.add_mem hφ hφ', fun x => by simp [e, e']⟩
  | smul c F _ hF =>
    obtain ⟨φ, hφ, e⟩ := hF
    exact ⟨c • φ, U₁.smul_mem c hφ, fun x => by simp [e]⟩

theorem pairSlice₂ {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {G : H E a b → ℂ}
    (hG : G ∈ pairSpace U₁ U₂) (x : GA E a) : ∃ φ ∈ U₂, ∀ y, φ.1 y = G (x, y) := by
  induction hG using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    exact ⟨φ₁.1 x • φ₂, U₂.smul_mem _ h₂, fun y => by simp⟩
  | zero => exact ⟨0, U₂.zero_mem, fun y => rfl⟩
  | add F F' _ _ hF hF' =>
    obtain ⟨φ, hφ, e⟩ := hF
    obtain ⟨φ', hφ', e'⟩ := hF'
    exact ⟨φ + φ', U₂.add_mem hφ hφ', fun y => by simp [e, e']⟩
  | smul c F _ hF =>
    obtain ⟨φ, hφ, e⟩ := hF
    exact ⟨c • φ, U₂.smul_mem c hφ, fun y => by simp [e]⟩

def pairSatEvA (y : GA E b) : (H E a b → ℂ) →ₗ[ℂ] (GA E a → ℂ) := LinearMap.funLeft ℂ ℂ fun x : GA E a => ((x, y) : H E a b)

def pairSatEvB (x : GA E a) : (H E a b → ℂ) →ₗ[ℂ] (GA E b → ℂ) := LinearMap.funLeft ℂ ℂ fun y : GA E b => ((x, y) : H E a b)

theorem pairSatEvA_equiv (w : Pl E) (y : GA E b) (g : GLw a w) (F : H E a b → ℂ) :
    pairSatEvA y (((pairRt a b w).comp (MonoidHom.inl _ _)) g F) =
      ((rightReg ℂ (GA E a) ℂ).comp (embW a w)) g (pairSatEvA y F) := by
  funext x
  show F ((x, y) * (embW a w g, embW b w 1)) = F (x * embW a w g, y)
  rw [map_one, Prod.mk_mul_mk, mul_one]

theorem pairSatEvB_equiv (w : Pl E) (x : GA E a) (g : GLw b w) (F : H E a b → ℂ) :
    pairSatEvB x (((pairRt a b w).comp (MonoidHom.inr _ _)) g F) =
      ((rightReg ℂ (GA E b) ℂ).comp (embW b w)) g (pairSatEvB x F) := by
  funext y
  show F ((x, y) * (embW a w 1, embW b w g)) = F (x, y * embW b w g)
  rw [map_one, Prod.mk_mul_mk, mul_one]

end Pair

theorem pairSat_holds : PairSat := by
  intro hT E _ _ _ a b s₁ s₂ Pa Pb w G g₁ g₂ u₁ u₂ t₁ t₂ hG h0 hf
  obtain ⟨⟨x₀, y₀⟩, hp⟩ : ∃ p, G p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (funext hc)
  have fixA : ∀ y (φ : Sm E a), (∀ x, φ.1 x = G (x, y)) → ∀ k ∈ KGL w (n := a), finRep E a (locGL E a w k) φ = φ := by
    intro y φ e k hk
    refine Subtype.ext (funext fun x => ?_)
    show φ.1 (x * finGL E a (locGL E a w k)) = φ.1 x
    have := congrFun (GlobalTheory.LGrp.mem_fixed.1 hf (k, 1) (Subgroup.mem_prod.2 ⟨hk, one_mem _⟩)) (x, y)
    change G ((x, y) * (embW a w k, embW b w 1)) = G (x, y) at this
    rw [map_one, Prod.mk_mul_mk, mul_one] at this
    rw [e, e]
    exact this
  have fixB : ∀ x (φ : Sm E b), (∀ y, φ.1 y = G (x, y)) → ∀ k ∈ KGL w (n := b), finRep E b (locGL E b w k) φ = φ := by
    intro x φ e k hk
    refine Subtype.ext (funext fun y => ?_)
    show φ.1 (y * finGL E b (locGL E b w k)) = φ.1 y
    have := congrFun (GlobalTheory.LGrp.mem_fixed.1 hf (1, k) (Subgroup.mem_prod.2 ⟨one_mem _, hk⟩)) (x, y)
    change G ((x, y) * (embW a w 1, embW b w k)) = G (x, y) at this
    rw [map_one, Prod.mk_mul_mk, mul_one] at this
    rw [e, e]
    exact this
  obtain ⟨φa, hφa, ea⟩ := pairSlice₁ hG y₀
  obtain ⟨φb, hφb, eb⟩ := pairSlice₂ hG x₀
  have na : φa ≠ 0 := fun h => hp (by rw [← ea x₀, h]; rfl)
  have nb : φb ≠ 0 := fun h => hp (by rw [← eb y₀, h]; rfl)
  obtain ⟨Ba, sa, hBa⟩ := hT E a s₁ Pa w g₁ u₁ t₁ ⟨φa, hφa, na, fixA y₀ φa ea⟩
  obtain ⟨Bb, sb, hBb⟩ := hT E b s₂ Pb w g₂ u₂ t₂ ⟨φb, hφb, nb, fixB x₀ φb eb⟩
  have eigA : ∀ ϖ, IsUnifV E w ϖ → ∀ i ≤ a, heckeVec ((pairRt a b w).comp (MonoidHom.inl _ _)) (KGL w (n := a))
      (Tj ℂ a (Ov E w) ϖ i) G = satEig (qV E w) a Ba i • G := by
    intro ϖ hϖ i hi
    funext ⟨x, y⟩
    obtain ⟨φ, hφ, e⟩ := pairSlice₁ hG y
    have key := congrFun (map_heckeVec (Final.GLintComm E w a) (Tj_mem_hecke hϖ i) (pairSatEvA y)
      (ρ := (pairRt a b w).comp (MonoidHom.inl _ _)) (ρ' := (rightReg ℂ (GA E a) ℂ).comp (embW a w))
      (pairSatEvA_equiv w y) G) x
    have hev : pairSatEvA y G = φ.1 := funext fun x => (e x).symm
    rw [hev] at key
    change heckeVec ((pairRt a b w).comp (MonoidHom.inl _ _)) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ i) G (x, y) = _ at key
    rw [key, Pi.smul_apply, ← e x]
    by_cases hz : φ = 0
    · subst hz
      simp [heckeVec_zero_pair]
    · have hs := (hBa φ hφ hz (fixA y φ e)).map (Sm E a).subtype
        (ρ' := (rightReg ℂ (GA E a) ℂ).comp (embW a w)) (fun g z => rfl) (by simpa using hz)
      have he : heckeVec ((rightReg ℂ (GA E a) ℂ).comp (embW a w)) (KGL w (n := a)) (Tj ℂ a (Ov E w) ϖ i) φ.1 =
          satEig (qV E w) a Ba i • φ.1 := hs.2.2.2 ϖ hϖ i hi
      rw [he]
      rfl
  have eigB : ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ b, heckeVec ((pairRt a b w).comp (MonoidHom.inr _ _)) (KGL w (n := b))
      (Tj ℂ b (Ov E w) ϖ j) G = satEig (qV E w) b Bb j • G := by
    intro ϖ hϖ j hj
    funext ⟨x, y⟩
    obtain ⟨φ, hφ, e⟩ := pairSlice₂ hG x
    have key := congrFun (map_heckeVec (Final.GLintComm E w b) (Tj_mem_hecke hϖ j) (pairSatEvB x)
      (ρ := (pairRt a b w).comp (MonoidHom.inr _ _)) (ρ' := (rightReg ℂ (GA E b) ℂ).comp (embW b w))
      (pairSatEvB_equiv w x) G) y
    have hev : pairSatEvB x G = φ.1 := funext fun y => (e y).symm
    rw [hev] at key
    change heckeVec ((pairRt a b w).comp (MonoidHom.inr _ _)) (KGL w (n := b)) (Tj ℂ b (Ov E w) ϖ j) G (x, y) = _ at key
    rw [key, Pi.smul_apply, ← e y]
    by_cases hz : φ = 0
    · subst hz
      simp [heckeVec_zero_pair]
    · have hs := (hBb φ hφ hz (fixB x φ e)).map (Sm E b).subtype
        (ρ' := (rightReg ℂ (GA E b) ℂ).comp (embW b w)) (fun g z => rfl) (by simpa using hz)
      have he : heckeVec ((rightReg ℂ (GA E b) ℂ).comp (embW b w)) (KGL w (n := b)) (Tj ℂ b (Ov E w) ϖ j) φ.1 =
          satEig (qV E w) b Bb j • φ.1 := hs.2.2.2 ϖ hϖ j hj
      rw [he]
      rfl
  refine ⟨Ba, Bb, sa, sb, hf, (hBa φa hφa na (fixA y₀ φa ea)).2.2.1, (hBb φb hφb nb (fixB x₀ φb eb)).2.2.1,
    fun ϖ hϖ i hi j hj => ?_⟩
  rw [heckeVec_pairProd _ (Final.GLintComm E w a) (Final.GLintComm E w b) (Tj_mem_hecke hϖ i) (Tj_mem_hecke hϖ j) hf,
    eigB ϖ hϖ j hj, heckeVec_smul_pair _ (Final.GLintComm E w a) (Tj_mem_hecke hϖ i), eigA ϖ hϖ i hi, smul_smul,
    mul_comm]

end PositivityTheory.Rg.BcB.F.RS
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PTreeModOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tw_zero' {N : ℕ} (V : Submodule ℂ (Sm E N)) : tw V 0 = V := by
  unfold tw
  have h : GlobalTheory.CuspRep.Model.absC E 0 = 1 := by
    apply Subtype.ext; ext x
    simp [GlobalTheory.CuspRep.Model.absC, GlobalTheory.Mem.Chr.CharModel.absHom]
  rw [h]
  convert Submodule.map_id V
  ext φ x
  simp [mulChi, chiDet]

theorem twPart_one (x : Σ M : ℕ, Submodule ℂ (Sm E M)) : twPart 1 x = x := by
  obtain ⟨M, V⟩ := x
  simp only [twPart]
  congr 1
  convert Submodule.map_id V
  ext φ x
  simp [mulChi, chiDet]

theorem twRep_of_one {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (hχ : ∀ g, χ g = 1) : twRep ρ χ = ρ := by
  ext g x
  simp [twRep_apply, hχ]

theorem Sep.equiv {G V X Y : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] {_ : AddCommGroup X}
    {_ : Module ℂ X} {_ : AddCommGroup Y} {_ : Module ℂ Y} {ρ : Representation ℂ G V} {S : Submodule ℂ V}
    {τ : Representation ℂ G X} {τ' : Representation ℂ G Y} (h : Sep ρ S τ) (e : τ.Equiv τ') : Sep ρ S τ' := by
  obtain ⟨hS, J, L, hL, hinj⟩ := h
  refine ⟨hS, J, fun j => e.toLinearMap ∘ₗ L j, fun j g x hx hs => ?_, fun x hx hs h0 => hinj x hx hs fun j => ?_⟩
  · simp only [LinearMap.comp_apply, hL j g x hx hs]
    exact LinearMap.congr_fun (e.isIntertwining' g) (L j x)
  · exact e.toLinearEquiv.injective ((h0 j).trans (map_zero _).symm)

theorem Sep.equiv_symm {G V X Y : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] {_ : AddCommGroup X}
    {_ : Module ℂ X} {_ : AddCommGroup Y} {_ : Module ℂ Y} {ρ : Representation ℂ G V} {S : Submodule ℂ V}
    {τ : Representation ℂ G X} {τ' : Representation ℂ G Y} (h : Sep ρ S τ) (e : τ'.Equiv τ) : Sep ρ S τ' :=
  h.equiv e.symm

theorem sep_of_subsingleton {G V X : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X]
    [Module ℂ X] (ρ : Representation ℂ G V) (S : Submodule ℂ V) (τ : Representation ℂ G X) (hG : ∀ g : G, g = 1)
    (hX : Nontrivial X) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ x ∈ S, ℓ x = 0 → x = 0) : Sep ρ S τ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : X)
  refine ⟨fun g x hx => by rw [hG g, map_one]; exact hx, Unit, fun _ => ℓ.smulRight v,
    fun _ g x _ _ => by rw [hG g, map_one, map_one]; rfl,
    fun x hx _ h0 => hℓ x hx ((smul_eq_zero.1 (h0 ())).resolve_right hv)⟩

theorem equiv_untwist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (f : a ⊕ b ≃ n)
    {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (τ : Representation ℂ (GL n k) Z) (π₁ : Representation ℂ (GL a k) X) (π₂ : Representation ℂ (GL b k) Y)
    (χ₁ : GL a k →* ℂˣ) (χ₂ : GL b k →* ℂˣ) (h₁ : ∀ g, χ₁ g = 1) (h₂ : ∀ g, χ₂ g = 1)
    (e : τ.Equiv (GlobalTheory.SmGL.ind₂ f (GlobalTheory.SmGL.extTensor (twRep π₁ χ₁) (twRep π₂ χ₂)))) :
    Nonempty (τ.Equiv (GlobalTheory.SmGL.ind₂ f (GlobalTheory.SmGL.extTensor π₁ π₂))) := by
  rw [twRep_of_one π₁ χ₁ h₁, twRep_of_one π₂ χ₂ h₂] at e
  exact ⟨e⟩

theorem sep_rank0 (w : Pl E) (S : Submodule ℂ (Sm E 0)) (P : Pre E 0) :
    Sep ((finRep E 0).comp (locGL E 0 w)) S (lp P w) := by
  refine sep_of_subsingleton _ _ _ (fun g => Units.ext (Subsingleton.elim _ _))
    (GlobalTheory.PfBCI.nontrivial_locProd P.h w (P.σ · w)) ((LinearMap.proj 1).comp (Sm E 0).subtype) ?_
  intro x _ h
  apply Subtype.ext; funext g
  obtain rfl : g = 1 := Units.ext (Subsingleton.elim _ _)
  exact h

theorem sep_leaf_pos (hL : LeafMod) (w : Pl E) {M : ℕ} (V : Submodule ℂ (Sm E M)) (hV : IsDiscrete V) (hM : 0 < M)
    (P : Pre E M) (hp : TreeParts (Tr.leaf V 0) P) : Sep ((finRep E M).comp (locGL E M w)) V (lp P w) := by
  obtain ⟨c, N, h, V', σ, m, pos, disc, loc, inf⟩ := P
  have hp' : List.ofFn (fun i => (⟨N i, V' i⟩ : Σ M, Submodule ℂ (Sm E M))) = [⟨M, V⟩] := by
    unfold TreeParts at hp
    rw [hp]
    simp [Tr.leafList, hM]
  have hc : c = 1 := by simpa using congrArg List.length hp'
  subst hc
  obtain ⟨d, rfl⟩ : ∃ d, N = fun _ => d := ⟨N 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨s, rfl⟩ : ∃ s, σ = fun _ => s := ⟨σ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have h0 : (⟨d, V' 0⟩ : Σ M, Submodule ℂ (Sm E M)) = ⟨M, V⟩ := by simpa using hp'
  obtain ⟨rfl, hVV⟩ := Sigma.mk.inj_iff.1 h0
  obtain rfl := eq_of_heq hVV
  obtain ⟨e⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one (s w).smooth (GlobalTheory.SmGL.stdBlocks (fun _ => d) h)
    (fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val, Subsingleton.elim a 0]; simp))
  exact Sep.equiv (hL E d (V' 0) w (s w) (disc 0) (loc 0 w)) e

theorem sum_leafList : ∀ {N : ℕ} (t : Tr E N), ((t.leafList.filter fun x => 0 < x.1).map (·.1)).sum = N
  | M, .leaf V z => by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp [Tr.leafList]
    · simp [Tr.leafList, h]
  | _, .node t₁ t₂ => by simp [Tr.leafList, List.filter_append, sum_leafList t₁, sum_leafList t₂]

def Pre.restr {n : ℕ} (P : Pre E n) {k r : ℕ} (ι : Fin k → Fin P.c) (h : ∑ i, P.N (ι i) = r) : Pre E r where
  c := k
  N i := P.N (ι i)
  h := h
  V i := P.V (ι i)
  σ i := P.σ (ι i)
  m i := P.m (ι i)
  pos i := P.pos _
  discrete i := P.discrete _
  loc i := P.loc _
  inf i := P.inf _

theorem exists_split {n r s : ℕ} (P : Pre E n) (A B : List (Σ M : ℕ, Submodule ℂ (Sm E M))) (hAB : parts P = A ++ B)
    (hA : (A.map (·.1)).sum = r) (hB : (B.map (·.1)).sum = s) :
    ∃ (P₁ : Pre E r) (P₂ : Pre E s), parts P₁ = A ∧ parts P₂ = B := by
  have hlen : P.c = A.length + B.length := by simpa [parts] using congrArg List.length hAB
  have key : ∀ k (hk : k < P.c), (⟨P.N ⟨k, hk⟩, P.V ⟨k, hk⟩⟩ : Σ M, Submodule ℂ (Sm E M)) =
      (A ++ B)[k]'(by simp; omega) := fun k hk => by
    have := List.getElem_of_eq hAB (i := k) (by simp [parts]; exact hk)
    simpa [parts] using this
  let ι₁ : Fin A.length → Fin P.c := fun i => ⟨i, by omega⟩
  let ι₂ : Fin B.length → Fin P.c := fun j => ⟨A.length + j, by omega⟩
  have e₁ : List.ofFn (fun i => (⟨P.N (ι₁ i), P.V (ι₁ i)⟩ : Σ M, Submodule ℂ (Sm E M))) = A := by
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    rw [List.getElem_ofFn]
    exact (key k _).trans (List.getElem_append_left hk2)
  have e₂ : List.ofFn (fun i => (⟨P.N (ι₂ i), P.V (ι₂ i)⟩ : Σ M, Submodule ℂ (Sm E M))) = B := by
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    rw [List.getElem_ofFn]
    refine (key _ _).trans ?_
    rw [List.getElem_append_right (by omega)]
    simp
  have s₁ : ∑ i, P.N (ι₁ i) = r := by
    have := congrArg (fun l => (l.map (·.1)).sum) e₁
    simp only [List.map_ofFn, List.sum_ofFn] at this
    rw [← hA, ← this]; rfl
  have s₂ : ∑ i, P.N (ι₂ i) = s := by
    have := congrArg (fun l => (l.map (·.1)).sum) e₂
    simp only [List.map_ofFn, List.sum_ofFn] at this
    rw [← hB, ← this]; rfl
  exact ⟨Pre.restr P ι₁ s₁, Pre.restr P ι₂ s₂, e₁, e₂⟩

theorem tree_module_separation (hL : LeafMod) (hN : NodeMod) (hJ : JoinMod) (w : Pl E) :
    ∀ {N : ℕ} (t : Tr E N) (P : Pre E N), t.Good → t.Untw → TreeParts t P →
      Sep ((finRep E N).comp (locGL E N w)) t.space (lp P w) := by
  intro N t
  induction t with
  | leaf V z =>
    intro P hg hu hp
    have hz : z = 0 := hu z (by simp [Tr.twists])
    subst hz
    show Sep _ (tw V 0) _
    rw [tw_zero']
    rcases hg with ⟨hM, -, -⟩ | ⟨hM, hV, -⟩
    · subst hM; exact sep_rank0 w V P
    · exact sep_leaf_pos hL w V hV hM P hp
  | node t₁ t₂ ih₁ ih₂ =>
    intro P hg hu hp
    obtain ⟨g₁, g₂⟩ := hg
    have u₁ : t₁.Untw := fun z hz => hu z (List.mem_append_left _ hz)
    have u₂ : t₂.Untw := fun z hz => hu z (List.mem_append_right _ hz)
    have hp' : parts P = (t₁.leafList.filter fun x => 0 < x.1) ++ (t₂.leafList.filter fun x => 0 < x.1) := by
      rw [← List.filter_append]; exact hp
    obtain ⟨P₁, P₂, h₁, h₂⟩ := exists_split P _ _ hp' (sum_leafList t₁) (sum_leafList t₂)
    have hj : IsJoin 1 1 P₁ P₂ P := by
      unfold IsJoin
      rw [hp', h₁, h₂]
      have : twPart (E := E) 1 = id := funext twPart_one
      rw [this, List.map_id, List.map_id]
    obtain ⟨e⟩ := equiv_untwist (e := (hJ E _ _ _ rfl 1 1 P₁ P₂ P w hj).some)
      (h₁ := fun _ => by simp [HChar.loc])
      (h₂ := fun _ => by simp [HChar.loc])
    exact Sep.equiv_symm (hN E _ _ t₁ t₂ w _ _ _ _ (ih₁ P₁ g₁ u₁ h₁) (ih₂ P₂ g₂ u₂ h₂)) e

theorem treeModOf_holds : TreeModOf :=
  fun hL hN hJ _ _ _ _ _ t P w hg hu hp => tree_module_separation hL hN hJ w t P hg hu hp

end PositivityTheory.Rg.BcB.F.RS

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PTreeSatOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

theorem tso_map_heckeVec {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G X} {K : Subgroup G} {h : G → ℂ} (hK : IsCommensurated K)
    (hh : h ∈ Hecke ℂ K) (L : V →ₗ[ℂ] X) {x : V} (hL : ∀ g, L (ρ g x) = τ g (L x)) :
    L (heckeVec ρ K h x) = heckeVec τ K h (L x) := by
  refine (L.toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ x)).trans (finsum_congr fun c => ?_)
  simp [hL]

theorem tso_heckeVec_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {h : G → ℂ} (S : Submodule ℂ V) (hS : ∀ g, ∀ y ∈ S, ρ g y ∈ S) {x : V} (hx : x ∈ S) :
    heckeVec ρ K h x ∈ S := by
  unfold heckeVec
  exact finsum_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem) fun c => S.smul_mem _ (hS _ _ hx)

theorem tso_heckeVec_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {h : G → ℂ} : heckeVec ρ K h 0 = 0 := by
  simp [heckeVec]

theorem treeSatOf_holds : TreeSatOf := by
  intro hT E _ _ _ N t P w hg hu htp ⟨φ0, hφ0S, hφ00, hφ0K⟩
  obtain ⟨hinv, J, L, heq, hsep⟩ := hT E N t P w hg hu htp
  have hKo := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w N).1
  have hKc := Final.GLintComm E w N
  have fixK : ∀ φ, (∀ k ∈ KGL w (n := N), finRep E N (locGL E N w k) φ = φ) →
      φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) :=
    fun φ h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => h k hk
  have smK : ∀ φ, φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) → SmVec ((finRep E N).comp (locGL E N w)) φ :=
    fun φ h => ⟨_, hKo, h⟩
  have hLfix : ∀ j φ, φ ∈ t.space → φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) →
      L j φ ∈ fixed (lp P w) (KGL w (n := N)) := fun j φ hS hf =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← heq j k φ hS (smK _ hf), GlobalTheory.LGrp.mem_fixed.1 hf k hk]
  obtain ⟨j, hj⟩ : ∃ j, L j φ0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hφ00 (hsep φ0 hφ0S (smK _ (fixK _ hφ0K)) hc)
  obtain ⟨b, hb, -⟩ := GlobalTheory.SatInd.exists_sat_multiProd P.h (π := fun i => (P.σ i w).ρ) (fun i => (P.σ i w).smooth)
    (fun i => (P.σ i w).irred) (hLfix j φ0 hφ0S (fixK _ hφ0K)) hj
  have hvec : ∀ f ∈ fixed (lp P w) (KGL w (n := N)), f ≠ 0 → IsSatVecGL w (lp P w) f (∑ i, b i) := fun f hf hf0 => by
    obtain ⟨S, hS, hfS⟩ := GlobalTheory.SatInd.exists_sat_multiProd P.h (π := fun i => (P.σ i w).ρ)
      (fun i => (P.σ i w).smooth) (fun i => (P.σ i w).irred) hf hf0
    have e : S = b := funext fun a => (hS a).unique (hb a)
    rw [← e]
    exact hfS
  have hcard : (∑ i, b i).card = N := (hvec _ (hLfix j φ0 hφ0S (fixK _ hφ0K)) hj).2.2.1
  refine ⟨_, ⟨b, fun i => ⟨(hb i).1, hb i⟩, rfl⟩, fun φ hφS hφ0 hφK => ?_⟩
  have hf := fixK _ hφK
  refine ⟨hφ0, hf, hcard, fun ϖ hϖ i hi => ?_⟩
  have hh := GlobalTheory.LFun.Tj_mem_hecke (n := N) hϖ i
  have hTS := tso_heckeVec_mem (K := KGL w (n := N)) (h := Tj ℂ N (Ov E w) ϖ i) t.space hinv hφS
  have hTf := GlobalTheory.LFun.SatCompare.heckeVec_mem_fixed hKc hh hf
  refine sub_eq_zero.1 (hsep _ (t.space.sub_mem hTS (t.space.smul_mem _ hφS))
    (smK _ (sub_mem hTf (Submodule.smul_mem _ _ hf))) fun j' => ?_)
  have key := tso_map_heckeVec (τ := lp P w) hKc hh (L j') fun g => heq j' g φ hφS (smK _ hf)
  rw [LinearMap.map_sub, LinearMap.map_smul]
  refine sub_eq_zero.2 (key.trans ?_)
  by_cases h0 : L j' φ = 0
  · exact (congrArg (heckeVec (lp P w) (KGL w (n := N)) (Tj ℂ N (Ov E w) ϖ i)) h0).trans
      (tso_heckeVec_zero.trans ((smul_zero _).symm.trans (congrArg _ h0.symm)))
  · exact (hvec _ (hLfix j' φ hφS hf) h0).2.2.2 ϖ hϖ i hi

end PositivityTheory.Rg.BcB.F.RS

end
end


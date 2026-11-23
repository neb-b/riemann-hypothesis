module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ContinuousIffCrdA
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
section
noncomputable section

namespace GlobalTheory.Member.PrincLevel

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem smul_mem_hat (L : Set (Fin n → E)) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat F L) : a • z ∈ GlobalTheory.AdLat.hat F L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, x, hx, ?_⟩
    · exact mul_mem (ha v) (hb v)
    · funext i
      simp only [Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def congSub {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (H : AddSubgroup (Fin n → R)) (N : ℕ) :
    AddSubgroup (Fin n → R) where
  carrier := {z | ∃ y ∈ H, M *ᵥ z - z = N • y}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    refine ⟨x + y, add_mem hx hy, ?_⟩
    rw [Matrix.mulVec_add, smul_add, ← ha, ← hb]; abel
  neg_mem' := by
    rintro a ⟨x, hx, ha⟩
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.mulVec_neg, smul_neg, ← ha]; abel

theorem cong_of_gen (L : Set (Fin n → E)) (S : Set (Fin n → E)) (hS : L ⊆ AddSubgroup.closure S)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (N : ℕ)
    (h : ∀ x ∈ S, ∃ y ∈ GlobalTheory.AdLat.hat F L, M *ᵥ GlobalTheory.AdLat.fv F x - GlobalTheory.AdLat.fv F x = N • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, M *ᵥ z - z = N • y := by
  have h1 : ∀ x ∈ AddSubgroup.closure S, GlobalTheory.AdLat.fv F x ∈ congSub M (GlobalTheory.AdLat.hat F L) N := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem z hz => exact h z hz
    | zero =>
      have : GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := by funext i; simp [GlobalTheory.AdLat.fv]
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : GlobalTheory.AdLat.fv F (x + y) = GlobalTheory.AdLat.fv F x + GlobalTheory.AdLat.fv F y := by
        funext i; simp [GlobalTheory.AdLat.fv, TensorProduct.tmul_add]
      rw [this]; exact add_mem hx hy
    | neg x _ hx =>
      have : GlobalTheory.AdLat.fv F (-x) = -GlobalTheory.AdLat.fv F x := by
        funext i; simp [GlobalTheory.AdLat.fv, TensorProduct.tmul_neg]
      rw [this]; exact neg_mem hx
  have h2 : GlobalTheory.AdLat.hat F L ≤ congSub M (GlobalTheory.AdLat.hat F L) N := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := h1 x (hS hx)
    have hz : (fun i => a ⊗ₜ[F] x i : Fin n → GlobalTheory.AdLat.RA F E) = a • GlobalTheory.AdLat.fv F x := by
      funext i
      simp only [GlobalTheory.AdLat.fv, Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    refine ⟨a • y, smul_mem_hat L a ha hy, ?_⟩
    rw [hz, Matrix.mulVec_smul, ← smul_sub, e, smul_comm]
  exact fun z hz => h2 hz

theorem continuous_mulVec_sub {X R : Type} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {f : X → Matrix (Fin n) (Fin n) R} (hf : Continuous f) (v : Fin n → R) :
    Continuous fun k => f k *ᵥ v - v :=
  (hf.matrix_mulVec continuous_const).sub continuous_const

end General

variable {D : D7}

theorem finCong_map {V : HSp D} {N : ℕ} {k : GA D V} (hk : FinCong V N k) :
    ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  rw [sub_eq_iff_eq_add] at e
  rw [e]
  exact add_mem (nsmul_mem hy N) hz

theorem finCong_one (V : HSp D) (N : ℕ) : FinCong V N 1 := by
  intro z _
  exact ⟨0, zero_mem _, by simp⟩

theorem finCong_mul {V : HSp D} {N : ℕ} {a b : GA D V} (ha : FinCong V N a) (hb : FinCong V N b) :
    FinCong V N (a * b) := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hb z hz
  obtain ⟨x, hx, e'⟩ := ha _ (finCong_map hb z hz)
  refine ⟨x + y, add_mem hx hy, ?_⟩
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← e, ← e']
  abel

theorem finCong_inv {V : HSp D} {N : ℕ} {a : GA D V} (ha : FinCong V N a) : FinCong V N a⁻¹ := by
  obtain ⟨h1, -, h3, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hinv : ∀ z ∈ latHat V, (finHom V a⁻¹).1 *ᵥ z ∈ latHat V := by
    have hm := finCong_map ha
    rw [h1] at hm ⊢
    rw [map_inv]
    exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latC V) (finHom V a) (cF D) h3 h4 hm
      (GlobalTheory.Member.finHom_herm_det D V a).2.1
  intro z hz
  obtain ⟨y, hy, e⟩ := ha _ (hinv z hz)
  refine ⟨-y, neg_mem hy, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at e
  rw [neg_nsmul, ← e, neg_sub]

def levelGroup (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | k ∈ GfC V ∧ FinCong V N k}
  one_mem' := ⟨one_mem _, finCong_one V N⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, finCong_mul ha.2 hb.2⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, finCong_inv ha.2⟩

theorem finCong_mem_nhds (V : HSp D) {N : ℕ} (hN : 0 < N) :
    {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V) := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨hop, hc, -⟩ := GlobalTheory.Member.latHat_open_and_continuous D V
  have : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨S, hS⟩ := h3.restrictScalars (R := ℤ)
  have hLS : (latC V : Set (Fin V.rank → D.host.E)) ⊆
      (AddSubgroup.closure (S : Set (Fin V.rank → D.host.E)) : AddSubgroup (Fin V.rank → D.host.E)) := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (S : Set (Fin V.rank → D.host.E)) := by rw [hS]; exact hx
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    exact hx'
  have hU : (⋂ x ∈ S, {k : GA D V | ∃ y ∈ latHat V,
      (finHom V k).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x = N • y}) ∈ 𝓝 (1 : GA D V) := by
    refine (Filter.biInter_finset_mem S).2 fun x _ => ?_
    have hcx : Continuous fun k : GA D V =>
        (finHom V k).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x :=
      continuous_mulVec_sub hc _
    refine ((hop N hN).preimage hcx).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hU fun k hk => ?_
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hk
  unfold FinCong
  rw [Set.mem_ofPred_eq]
  rw [h1] at hk ⊢
  exact cong_of_gen _ _ hLS _ N fun x hx => hk x hx

theorem exists_levelK_and_nhds : ∀ (D : D7) (V : HSp D), ∀ N : ℕ,
    (∃ Kf : Subgroup (GA D V), IsLevelK V N Kf) ∧
      (0 < N → {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V)) :=
  fun _ V N => ⟨⟨levelGroup V N, fun _ => Iff.rfl⟩, fun hN => finCong_mem_nhds V hN⟩

end GlobalTheory.Member.PrincLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemLevelKOfSameMarkAndFrame
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

private theorem fib_gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * (G.map τ * x.map (starRingEnd ℂ)) := by
  ext a b
  simp [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]

private theorem fib_cancel {R G : Type} [CommRing R] [Group G] {n : ℕ} (f : G →* GL (Fin n) R) (g g' : G) (N : ℕ)
    (p v w w' y : Fin n → R) (e : p - (f g).1 *ᵥ v = N • w) (e' : p - (f g').1 *ᵥ v = N • w')
    (ey : (f g).1 *ᵥ y = w - w') : (f (g⁻¹ * g')).1 *ᵥ v - v = N • y := by
  have e2 : (f g').1 *ᵥ v - (f g).1 *ᵥ v = N • ((f g).1 *ᵥ y) := by
    rw [ey, smul_sub, ← e, ← e']; abel
  have hi : ∀ z, (f g⁻¹).1 *ᵥ ((f g).1 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have e3 := congrArg (fun z => (f g⁻¹).1 *ᵥ z) e2
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hi] at e3
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact e3

theorem mem_level_of_mark_of_frame_eq : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ (Kf : Subgroup (GA D V)), IsLevelK V l.M Kf → ∀ h h' k γ γ', C.Mark h k γ → C.Mark h' k γ' → C.fr (γ * h) k = C.fr (γ' * h') k → (γ * h)⁻¹ * (γ' * h') ∈ Kf := by
  intro D H Dw l Xo c σ V r C hC Kf hK h h' k γ γ' hm hm' hfr
  obtain rfl : V.rank = r := C.hr
  obtain ⟨-, hL, hM⟩ := hm
  obtain ⟨-, hL', hM'⟩ := hm'
  generalize γ * h = g at *
  generalize γ' * h' = g' at *
  obtain ⟨hA, hG, -⟩ := _root_.GlobalTheory.Member.Arch.archM_spec D V C.θ hC.inf
  rw [hK]
  refine ⟨hG _ fun τ hτ => ?_, ?_⟩
  · have hΨ : τ ∈ (C.M.X k).Ψ := by
      rw [(hC.base.type k).2, hC.iota.rt, hC.iota.rt0]; exact hτ
    have hx : (C.x₀ τ).det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det (hC.orth k τ hΨ)
      simp only [fib_gram_eq, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul,
        Matrix.det_diagonal] at h1
      refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
      unfold sgn
      split_ifs <;> simp
    have h1 : archM V (C.θ τ) g * C.x₀ τ = archM V (C.θ τ) g' * C.x₀ τ := congrFun hfr ⟨τ, hΨ⟩
    have hu : IsUnit (C.x₀ τ) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hx)
    have h2 := hu.mul_right_cancel h1
    rw [(hA τ).2.1, ← h2, ← (hA τ).2.1, inv_mul_cancel, (hA τ).1]
  · have hlat : (latG V g : Set (Fin V.rank → D.host.E)) = latG V g' := by
      have e := hL.symm.trans hL'
      have e1 : (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast C.hr.symm) = id := rfl
      rwa [e1, Set.image_id, Set.image_id] at e
    have hhat : latGHat V g' = latGHat V g := by
      rw [(_root_.GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.2.1, (_root_.GlobalTheory.Member.latG_lattice_and_completion D V g').2.2.2.2.1, hlat]
    have himg := (_root_.GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.1
    rw [← (_root_.GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1] at himg
    refine ((_root_.GlobalTheory.Member.finCong_iff_half_and_kfHalf D H l V).1 _).2 ((((_root_.GlobalTheory.Member.AALev.congruences_agree D V) _).2 _ _).2 ?_)
    intro a ha
    rw [← hC.iota.emb.2, LinearMap.range_eq_map, ← Submodule.map_smul''] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨w, hw, e⟩ := hM b hb
    obtain ⟨w', hw', e'⟩ := hM' b hb
    rw [hhat] at hw'
    have hd : w - w' ∈ (latGHat V g : Set _) := sub_mem hw hw'
    rw [himg] at hd
    obtain ⟨y, hy, ey⟩ := hd
    exact ⟨y, hy, fib_cancel (finHom V) g g' l.M _ _ w w' y e e' ey⟩

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnit
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem reindex_finCongr_self {n : ℕ} {α : Type} (h : n = n) (A : Matrix (Fin n) (Fin n) α) :
    Matrix.reindex (finCongr h) (finCongr h) A = A := by
  ext a b
  rfl

theorem fr_orthonormal_unit : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat (C.fr h k) τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) ∧ C.fr h k ∈ (C.M.X k).dom ∧ (∀ τ i, ‖dmin (C.M.X k).Gm (C.fr h k) τ i‖ = 1) ∧ Continuous (fun u => C.fr u k) ∧ (∀ u ∈ GfC V, C.fr (h * u) k = C.fr h k) ∧ (∀ u, C.fr (h * u) k = rmul (C.fr h k) (archMat V C.th C.hr (fun k => C.fr 1 k) u k)) ∧ ∀ x : Frame (C.M.X k).Ψ r, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) → ∃ u ∈ GinfC V, C.fr u k = x := by
  intro D H Dw l Xo c σ V r C hC h k
  have hr := C.hr
  subst hr
  obtain ⟨hA, -, hL⟩ := _root_.GlobalTheory.Member.Arch.archM_spec D V C.θ hC.inf
  have hG : (C.M.X k).Gm = -V.gramᵀ := by
    rw [(hC.modelW k).1, reindex_finCongr_self]
  have hfr : ∀ u (τ : (C.M.X k).Ψ), mat (C.fr u k) τ = archM V (C.θ τ.1) u * C.x₀ τ.1 := fun u τ => rfl
  have hext : ∀ x y : Frame (C.M.X k).Ψ V.rank, (∀ τ, mat x τ = mat y τ) → x = y :=
    fun x y hxy => funext fun τ => hxy τ
  obtain ⟨-, h2, h3⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (C.M.X k).p0
    (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm
  obtain ⟨-, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (C.M.X k).p0
    (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm
  have horth : ∀ u (τ : (C.M.X k).Ψ), gram τ.1 (C.M.X k).Gm (mat (C.fr u k) τ) =
      Matrix.diagonal fun a : Fin V.rank => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ) := by
    intro u τ
    rw [hfr, h3 τ.1 _ _ (by rw [hG]; exact (hA τ.1).2.2.2.2 u)]
    exact hC.orth k τ.1 τ.2
  refine ⟨horth h, (h2 _ (horth h)).1, (h2 _ (horth h)).2, ?_, fun u hu => ?_, fun u => ?_, fun x hx => ?_⟩
  · refine continuous_pi fun τ => ?_
    exact (hA τ.1).2.2.2.1.matrix_mul (continuous_const (y := C.x₀ τ.1))
  · refine hext _ _ fun τ => ?_
    rw [hfr, hfr, (hA τ.1).2.1, (hA τ.1).2.2.1 u hu, mul_one]
  · refine hext _ _ fun τ => ?_
    have hd : IsUnit (C.x₀ τ.1).det := by
      have := ((h2 _ (horth 1)).1 τ).1
      rw [hfr, (hA τ.1).1, one_mul] at this
      exact isUnit_iff_ne_zero.2 this
    show _ = mat (C.fr h k) τ * ((mat (C.fr 1 k) τ)⁻¹ * archM V (C.θ τ.1) u * mat (C.fr 1 k) τ)
    rw [hfr, hfr, hfr, (hA τ.1).2.1, (hA τ.1).1, one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  · have hmem : ∀ τ : D.host.E →+* ℂ, τ ∈ (C.M.X k).Ψ ↔
        τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
      intro τ
      rw [(hC.base.type k).2 τ, hC.iota.rt, hC.iota.rt0]
    have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (C.M.X k).Ψ,
        uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x ⟨τ, hτ⟩ = u * C.x₀ τ := by
      intro τ
      by_cases hτ : τ ∈ (C.M.X k).Ψ
      · obtain ⟨u, hu⟩ := h4 τ (C.x₀ τ) (mat x ⟨τ, hτ⟩) (hC.orth k τ hτ)
          ((hx ⟨τ, hτ⟩).trans (hC.orth k τ hτ).symm)
        rw [hG] at hu
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' hτ⟩
    choose u hu using hex
    obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem τ).2 hτ)).1
    refine ⟨a, ha, hext _ _ fun τ => ?_⟩
    rw [hfr, hau τ.1 ((hmem τ.1).1 τ.2)]
    exact ((hu τ.1 τ.2).2).symm

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OnlySecondOfFormLaws
section
noncomputable section

namespace GlobalTheory.CoreLawsCompare

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def DatumSign {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) {r : ℕ} (V' : ConjugateFieldNorm.HSpace D.host.E r)
    (ε : ℤˣ) : Prop :=
  ∃ φ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), Function.Injective φ ∧
    LinearMap.range φ = ConjugateFieldNorm.latAt D.host.F D.host.AA V' 1 ∧
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (-D.host.xi0 * herm V'.Gm (φ x) (φ y))

theorem invProb_iff (V : HSp D) (hP : VolPairEx V) (hV : FinVol V) (ν : Measure (AutQ V)) :
    IsProbabilityMeasure ν ∧ RightInv V ν ↔ ν = muQ1 V := by
  have hp := volPair_isVolPair V hP
  obtain ⟨i1, i2, i3⟩ := _root_.GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary _ _ D.sp.cm.sig _ V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : (volPair V).1.IsHaarMeasure := hp.1.1
  have hV' := hV
  rw [FinVol, muQ_univ] at hV'
  have hq : muQ1 V = ((volPair V).1 (volPair V).2)⁻¹ • ((volPair V).1.restrict (volPair V).2).map (autMk V) := by
    rw [muQ1, if_pos (show _ ∧ _ from hV), muQ_univ]; rfl
  constructor
  · rintro ⟨h1, h2⟩
    rw [hq]
    exact _root_.GlobalTheory.LatticeQuotUniq.invariant_prob_eq _ (GQ V) _ _ hp.2 hV'.2 ν h2
  · rintro rfl
    refine ⟨inferInstance, fun h ρ hρ s hs => ?_⟩
    have hm := autMk_measurable V
    have e : autMk V ⁻¹' (ρ ⁻¹' s) = (· * h) ⁻¹' (autMk V ⁻¹' s) := by
      ext g; exact iff_of_eq (congrArg (· ∈ s) (hρ g))
    have hs' : MeasurableSet (ρ ⁻¹' s) := by
      change MeasurableSet (autMk V ⁻¹' (ρ ⁻¹' s))
      rw [e]; exact measurable_mul_const h (hm hs)
    have hri := GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) _ hp.2 hV'.1 hV'.2
    have : (volPair V).1.IsMulRightInvariant := ⟨hri⟩
    have hF : IsFundamentalDomain (GQ V) ((Equiv.mulRight h⁻¹) ⁻¹' (volPair V).2) (volPair V).1 :=
      hp.2.preimage_of_equiv (measurePreserving_mul_right _ h⁻¹).quasiMeasurePreserving (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) (volPair V).1
    rw [hq, Measure.smul_apply, Measure.smul_apply]
    congr 1
    rw [show ((volPair V).1.restrict (volPair V).2).map (autMk V) s = _ from
      congrArg (fun m : Measure (AutQ V) => m s) (GlobalTheory.AutQuotCheck.map_restrict_eq (GQ V) _ hp.2 hF),
      Measure.map_apply hm hs', Measure.map_apply hm hs, Measure.restrict_apply (hm hs'),
      Measure.restrict_apply (hm hs), e, ← measure_preimage_mul_right (volPair V).1 h (_ ∩ _ ⁻¹' _)]
    congr 1
    ext g
    simp

def SpaceW (T : Core D) : Prop := ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → T.V j σ = D.sp.W j

variable {T : Core D} (hW : SpaceW T)

variable (π : Fin 2 → 𝓞 D.host.E)

end GlobalTheory.CoreLawsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeLocallyTwoProjectiveFactorsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_of_cube_locally_two_projective_factors : ∀ (k : Type) [Field k] (X Y Z : Over (Sp k)) (x₀ : 𝟙_ (Over (Sp k)) ⟶ X) (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (z₀ : 𝟙_ (Over (Sp k)) ⟶ Z), Smooth X.hom → Smooth Y.hom → IsProper X.hom → IsProper Y.hom → IsProjBy X.hom → IsProjBy Y.hom → GeometricallyIntegral X.hom → GeometricallyIntegral Y.hom → ConnectedSpace Z.left → ∀ M : LB (X ⊗ Y ⊗ Z).left, M.IsLB → Triv (M.pull (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z))).left) → Triv (M.pull (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z))).left) → Triv (M.pull (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀))).left) → ∀ z : Z.left, ∃ V : Z.left.Opens, z ∈ V ∧ Triv (M.pull ((snd X (Y ⊗ Z) ≫ snd Y Z).left ⁻¹ᵁ V).ι) := by
  first | exact @GlobalTheory.CubeLocal.triv_locally_of_faces | exact GlobalTheory.CubeLocal.triv_locally_of_faces | (intros; apply GlobalTheory.CubeLocal.triv_locally_of_faces <;> assumption)
end


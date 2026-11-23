module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELFamily

section Pairing

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}

theorem weilIs_pow_left (hW : Out.WeilSt) {n : ℕ} {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) (m : ℕ) : Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := by
  induction m with
  | zero => rwa [zero_add, pow_one, pow_one]
  | succ m ih =>
    rw [pow_succ x, pow_succ c]
    exact (hW S P n T).2.1 _ _ _ _ _ ih h

theorem weilIs_lower (hW : Out.WeilSt) {n m : ℕ} (hm : 0 < m) (hu : IsUnit ((n * m : ℕ) : Γ(T.left, ⊤)))
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (n * m) = 1) (hy : y ^ (n * m) = 1)
    (h : Out.WeilIs P.A P.L ((n * m : ℕ) : ℤ) x y c) : Out.WeilIs P.A P.L n (x ^ m) (y ^ m) (c ^ m) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have h₁ := CommPairing.weilIs_symm P.isLB (weilIs_pow_left P hW (CommPairing.weilIs_symm P.isLB h) m)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₁
  exact ((hW S P n T).2.2.2 _ x _ _ hu hx (by rw [← pow_mul, mul_comm, hy])).1 h₁

theorem eq_one_of_weilIs_one {K : Type} [Field K] (hW : Out.WeilSt) {x : Sp K ⟶ S} {n : ℕ}
    {y : Over.mk x ⟶ P.A} {c : Kˣ} (h : Out.WeilIs P.A P.L n 1 y (unitOn c)) : c = 1 := by
  have h₁ := (hW S P n _).2.1 _ _ _ _ _ h h
  rw [_root_.mul_one] at h₁
  have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
  exact mul_eq_left.1 (weilIs_unique_fieldPoint S P.A P.L P.isLB K x n 1 y _ _ (e ▸ h₁) h)

end Pairing

theorem weilIs_of_lbIso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L (M.pull (𝟙 A : A ⟶ A).left)) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (hw : Out.WeilIs A M n x y c) : Out.WeilIs A L n x y c := by
  have h₁ : LBIso (lbPow L 1) (M.pull (𝟙 A : A ⟶ A).left) :=
    LBIso.trans (DVR.linComb_isLB _ hL _ _) hL (pull_isLB hM _) (lbIso_lbPow_one hL) h
  have := (weilIs_along_hom hG S A A (𝟙 A) L M 1 n T x y c c hA hA hL hM inferInstance h₁
    (by rwa [Category.comp_id, Category.comp_id])).1
  rwa [Nat.cast_one, _root_.mul_one] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g k : ℕ} {J : Type}
  {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {o : Type} [CommRing o] {b : TBase o k} {em : o →+* ℂ} {ρ : o}
  {S : Scheme.{0}} {s : S ⟶ Sp o}

theorem exists_fibre (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s} {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (x : Sp K ⟶ S) (tx : TObj g k J b (x ≫ s)) (τ : SAB H (Sp K)),
      p ∈ Set.range x ∧ TMap tx t x ∧ IsPEL D a bas ρ tx τ := by
  obtain ⟨K, _, x, hx, K₀, _, β, i, j, t₀, tx, tc, hj, hs, m₁, m₂, m₃, τ, hτ⟩ := hp
  obtain ⟨τ₀, h₀⟩ := _root_.GlobalTheory.PELDesc.isPEL_descends hL E H D g k J a bas o b ρ K₀ ℂ j β _ t₀ tc τ hcl
    (by rw [← hj]; exact Spec.map_comp _ _) m₃ hτ
  obtain ⟨τ', h'⟩ := PELPull.isPEL_pull E H D g k J a bas o b ρ _ _ _ _ _ t₀ tx τ₀ hs.symm m₂ h₀
  have : CharZero K₀ := j.charZero
  exact ⟨K, inferInstance, (i.charZero_iff i.injective).1 inferInstance, x, tx, τ', hx, m₁, h'⟩

theorem exists_fibre_map (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s} {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K) (x : Sp K ⟶ S) (τ : SAB H (Sp K)) (ψ : τ.G.left ⟶ t.A.left),
      p ∈ Set.range x ∧ IsGrpPullback τ.G t.A x ψ ∧ LBIso τ.PP.L (t.L.pull ψ) ∧
      (∀ j, (τ.act.act (a j)).left ≫ ψ = ψ ≫ (t.act j).left) ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (y : Sp Ω ⟶ Sp K) (β : o →+* Ω), y ≫ x ≫ s = spMap β →
        DetCond D τ.act y (β ρ) ∧ ∃ I : TateIso D Ω (Over.mk y ⟶ τ.G) (fun c z => z ≫ τ.act.act c)
            (fun n z z' c => Out.WeilIs τ.G τ.PP.L n z z' (unitOn c)),
          (I.ζ k : Ω) = β b.ζ ∧ ∀ i, (I.ev k (bas (Pi.single i 1))).left ≫ ψ = (y ≫ x) ≫ (t.pt i).left := by
  obtain ⟨K, _, _, x, tx, τ, hx, ⟨ψ, hψ, hψL, hpt, hact⟩, φ, hφ, hφL, hφa, hgeom⟩ := exists_fibre hL hcl hp
  refine ⟨K, inferInstance, inferInstance, x, τ, φ.hom.left ≫ ψ, hx,
    ((isGrpPullback_of_iso φ).comp hψ).congr (Category.id_comp x) rfl,
    hφL.trans τ.PP.isLB (pull_isLB tx.isLB _) (pull_isLB t.isLB _) (PELPull.lbIso_pull hψL _ rfl),
    fun j => ?_, fun Ω _ _ _ y β hy => ?_⟩
  · have h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (tx.act j).left :=
      congrArg (fun z => z.left) (hφa j)
    rw [← Category.assoc, h₁, Category.assoc, hact, Category.assoc]
  · obtain ⟨hdet, I, hI, hA⟩ := hgeom Ω y β hy
    refine ⟨hdet, I, hI, fun i => ?_⟩
    have h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = y ≫ (tx.pt i).left :=
      congrArg (fun z => z.left) (hA i)
    rw [← Category.assoc, h₁, Category.assoc, hpt, Category.assoc]

theorem exists_geom (hL : Out.Laws) (hcl : Subring.closure (Set.range a) = ⊤) {t : TObj g k J b s}
    (r : OAct (𝓞 E) t.A)
    (hr : ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ t.A.left) (act : OAct (𝓞 E) G),
      IsGrpPullback G t.A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (t.act j).left) →
      ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left) {p : S}
    (hp : p ∈ fromSet em (PELClass (b := b) D a bas ρ em) t) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K),
      p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D r x (β ρ) ∧
      ∃ I : TateIso D K (Over.mk x ⟶ t.A) (fun c z => z ≫ r.act c)
          (fun n z z' c => Out.WeilIs t.A t.L n z z' (unitOn c)),
        (I.ζ k : K) = β b.ζ ∧ ∀ i, I.ev k (bas (Pi.single i 1)) =
          (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i := by
  have := t.ab.comm
  obtain ⟨K, _, _, x, τ, ψ, ⟨q, hq⟩, hψ, hψL, hact, hgeom⟩ := exists_fibre_map hL hcl hp
  have hc := hr _ x τ.G ψ τ.act hψ hact
  let y : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))
  obtain ⟨β, hβ⟩ : ∃ β : o →+* AlgebraicClosure K, y ≫ x ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ x ≫ s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨hdet, I, hI, hA⟩ := hgeom _ y β hβ
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance, y ≫ x, β,
    ⟨(default : PrimeSpectrum (AlgebraicClosure K)), ?_⟩, (Category.assoc _ _ _).trans hβ, fun σ => ?_,
    ObjPull.tateMove (ObjPull.pushEquiv hψ (Over.mk y)).symm (fun c z => ?_) (fun n z z' c hz => ?_) I, hI,
    fun i => Over.OverMorphism.ext (hA i)⟩
  · exact (Scheme.Hom.comp_apply y x _).trans ((congrArg x (Subsingleton.elim (α := PrimeSpectrum K) _ _)).trans hq)
  · rw [← LiePull.lieMult_pull _ _ _ t.A τ.G x ψ r τ.act hψ hc _ y σ,
      ← LiePull.lieMult_pull _ _ _ t.A τ.G x ψ r τ.act hψ hc _ y σ]
    exact hdet σ
  · obtain ⟨z, rfl⟩ := (ObjPull.pushEquiv hψ (Over.mk y)).surjective z
    rw [MulEquiv.symm_apply_eq, MulEquiv.symm_apply_apply]
    apply Over.OverMorphism.ext
    show (z.left ≫ _) ≫ _ = (z.left ≫ _) ≫ _
    rw [Category.assoc, ← hc, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm _ _ t.A τ.G x ψ t.L τ.PP.L t.isLB τ.PP.isLB hψ hψL (Over.mk y) n _ _ z z' _
      (ObjPull.pushEquiv_symm_left hψ (Over.mk y) z).symm
      (ObjPull.pushEquiv_symm_left hψ (Over.mk y) z').symm).1 hz

theorem exists_isPEL_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (w w' : J), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), em ρ = H.rt0 → Function.Injective em → Dense (fromSet em (PELClass (b := b) D a bas ρ em) t) → ∃ τ : SAB H S, IsPEL D a bas ρ t τ := by
  intro hL _ hcube E _ _ _ H D g J a bas w w' _ _ hw _ hcl k o _ b em ρ S _ _ s t hρ hem hd
  have := t.ab.comm
  obtain ⟨r, hra, hr⟩ := _root_.GlobalTheory.oAct_spread_of_dense_fibres (𝓞 E) J a S t.A t.act hcl t.ab t.hom (hd.mono fun p hp => by
    obtain ⟨K, _, _, x, τ, ψ, hx, hψ, -, hact, -⟩ := exists_fibre_map hL hcl hp
    exact ⟨K, inferInstance, x, τ.G, inferInstance, ψ, τ.act, hx, hψ, hact⟩)
  have hadj := fun c => _root_.GlobalTheory.adjoint_cubeLB_of_dense_fibres hL.globalFns S t.A t.L (r.act c) (r.act (H.bar c)) t.ab t.isLB t.ample (r.hom _)
    (r.hom _) (hd.mono fun p hp => by
      obtain ⟨K, _, _, x, τ, ψ, hx, hψ, hψL, hact, -⟩ := exists_fibre_map hL hcl hp
      have hc := hr _ x τ.G ψ τ.act hψ hact
      exact ⟨K, inferInstance, x, τ.G, inferInstance, inferInstance, ψ, τ.PP.L, _, _, hx, hψ, τ.PP.isLB, hψL, hc _, hc _,
        τ.adj c⟩)
  have hprim := _root_.GlobalTheory.lbIso_cube_of_dense hL.globalFns S t.A t.L (r.act H.w0) t.ab t.isLB t.ample t.rigid (r.hom _)
    (hd.mono fun p hp => by
      obtain ⟨K, _, _, x, τ, ψ, hx, hψ, hψL, hact, -⟩ := exists_fibre_map hL hcl hp
      have hc := hr _ x τ.G ψ τ.act hψ hact
      exact ⟨K, inferInstance, x, τ.G, inferInstance, inferInstance, ψ, τ.PP.L, _, hx, hψ, τ.PP.isLB, hψL, hc _, τ.prim⟩)
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ := PrimNorm.exists_primitive_normalisation hL.globalFns E H _ t.A r t.L t.ab
    t.isLB (hcube _ t.pol t.L t.isLB) hadj
  have iso' : LBIso PP.L (t.L.pull (𝟙 t.A : t.A ⟶ t.A).left) := by
    refine LBIso.trans PP.isLB t.isLB (pull_isLB t.isLB _)
      (LBIso.trans PP.isLB (DVR.linComb_isLB _ t.isLB _ _) t.isLB iso hprim.symm) ?_
    exact (LBIso.chartPull (Geo.Tor.chartPullPull t.L (𝟙 _) (𝟙 _) rfl) (chartPullId t.L) (lbIso_refl t.isLB)).symm
  refine ⟨⟨t.A, isSemiAbelian_of_isAbelianScheme _ t.ab, r, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t.A)), iso', fun j => ?_, fun K _ _ _ x β hx => ⟨?_, ?_⟩⟩
  · show r.act (a j) ≫ 𝟙 _ = 𝟙 _ ≫ t.act j
    rw [hra, Category.comp_id, Category.id_comp]
  · refine _root_.GlobalTheory.DetSpread.detCond_of_dense E H D S t.A g r o s ρ t.dim (hem ?_) (hd.mono fun p hp => ?_) K x β hx
    · rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast]
    · obtain ⟨K, _, _, _, x, β, h₁, h₂, h₃, -⟩ := exists_geom hL hcl r hr hp
      exact ⟨K, inferInstance, inferInstance, inferInstance, x, β, h₁, h₂, h₃⟩
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    have := b.unit.map em
    simp [h] at this
  have hcard : ∀ n, 0 < n → Nat.card {z : Over.mk x ⟶ t.A // z ^ n = 1} = n ^ Module.finrank ℤ D.La := fun n hn => by
    rw [← bas.finrank_eq, Module.finrank_fin_fun]
    exact (hL.mulN S t.pol n hn).2.2.2.2 K x (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨I, hI, hA⟩ := _root_.GlobalTheory.TateTower.tateIso_of_levels E H D K (Over.mk x ⟶ t.A) (fun c z => z ≫ r.act c)
    (fun n z z' c => Out.WeilIs t.A t.L n z z' (unitOn c)) k (β b.ζ) _ (fun i => bas (Pi.single i 1))
    (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i) hk
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m z z' c hn hm hz hz' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact weilIs_lower t.pol hL.weil hm u' hz hz' h)
    (fun m hm => by
      have hn := Nat.mul_pos hk hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := _root_.GlobalTheory.exists_levelIsometry_of_dense hL E H D S t.pol r.act o s b.ζ _
        (fun i => bas (Pi.single i 1)) t.pt (k * m) m hn (hd.mono fun p hp => by
          obtain ⟨K, _, _, _, x, β, h₁, h₂, -, I, h₃, h₄⟩ := exists_geom hL hcl r hr hp
          exact ⟨K, inferInstance, x, β, I.ζ (k * m), I.ev (k * m), Nat.cast_ne_zero.2 hn.ne', h₁, h₂, I.ζ_prim _ hn,
            I.add _, fun v => (I.onto _ hn _).2 ⟨v, rfl⟩, I.lin _, I.isom _ hn,
            by rw [← h₃, ← I.ζ_pow k m hk hm, Units.val_pow_eq_pow_val],
            fun i => (I.tower k m hk hm _).trans (h₄ i)⟩) K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := _root_.GlobalTheory.TorsIsometry.ker_and_onto E H D K (Over.mk x ⟶ t.A)
        (fun z z' c => Out.WeilIs t.A t.L (k * m : ℕ) z z' (unitOn c)) (k * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => eq_one_of_weilIs_one t.pol hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, h₇⟩)
  exact ⟨{ I with isom := fun n hn z z' => weilIs_of_lbIso hL.globalFns t.ab PP.isLB t.isLB iso' (I.isom n hn z z') },
    hI, fun i => (Category.comp_id _).trans (hA i)⟩

end GlobalTheory.PELFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsComplexPELObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPeriod

theorem linear_eq_zero_of_mem_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, F z ∈ Λ) (z : Fin g → ℂ) : F z = 0 := by
  have hc : Continuous fun w => (⟨F w, h w⟩ : Λ) := F.continuous_of_finiteDimensional.subtype_mk _
  have := PreconnectedSpace.constant inferInstance hc (x := z) (y := 0)
  simpa using congrArg Subtype.val this

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {z w : Fin g → ℂ} (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  rw [← u.ker]
  have := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at this
  exact mul_eq_right.1 this.symm


open Matrix in
theorem exists_coord {g : ℕ} {La La' : Type} [AddCommGroup La] [AddCommGroup La'] (Q : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : La' ≃+ La) (Q' : La' →+ (Fin g → ℂ))
    (hQ : ∀ x, h (Q' x) = Q (e x)) (inj : Function.Injective Q) (disc : DiscreteTopology Q.range)
    (span : Submodule.span ℝ (Set.range Q) = ⊤) (herm : Hm.IsHermitian)
    (pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    ∃ Hm' : Matrix (Fin g) (Fin g) ℂ, Function.Injective Q' ∧ DiscreteTopology Q'.range ∧
      Submodule.span ℝ (Set.range Q') = ⊤ ∧ Hm'.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧
      ∀ x y, hermForm Hm' (Q' x) (Q' y) = hermForm Hm (Q (e x)) (Q (e y)) := by
  let L := h.toLinearMap
  let M := LinearMap.toMatrix' L
  have key : ∀ z w, hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec L z, ← LinearMap.toMatrix'_mulVec L w, hermForm, hermForm, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, star_mulVec, ← mulVec_transpose]
    rfl
  refine ⟨Mᵀ * Hm * Mᵀᴴ, fun x y hxy => e.injective (inj (by rw [← hQ, ← hQ, hxy])), ?_, ?_,
    isHermitian_mul_mul_conjTranspose _ herm, fun z hz => ?_, fun x y => ?_⟩
  · let m : Q'.range → Q.range := fun z => ⟨h z, by
      obtain ⟨_, x, rfl⟩ := z
      exact ⟨e x, (hQ x).symm⟩⟩
    have hm : Continuous m :=
      (L.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hm fun z w hzw =>
      Subtype.ext (h.injective (congrArg Subtype.val hzw))
  · have r : Set.range Q' = (h.symm.toLinearMap.restrictScalars ℝ) '' Set.range Q := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨_, ⟨e x, rfl⟩, by simp [← hQ]⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨e.symm x, h.injective (by simp [hQ])⟩
    rw [r, Submodule.span_image, span, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  · rw [key]
    exact pos _ fun h0 => hz (h.injective (h0.trans (map_zero h).symm))
  · rw [key, ← hQ, ← hQ]
    rfl

theorem exists_module {O : Type} [CommRing O] {g : ℕ} {La : Type} [AddCommGroup La] (ty : Fin g → (O →+* ℂ))
    (Q : La →+ (Fin g → ℂ)) (inj : Function.Injective Q) (st : ∀ c x, ∃ y, ∀ i, Q y i = ty i c * Q x i) :
    ∃ _ : Module O La, ∀ (c : O) x i, Q (c • x) i = ty i c * Q x i := by
  choose sm hsm using st
  letI : SMul O La := ⟨sm⟩
  have hs : ∀ (c : O) x i, Q (c • x) i = ty i c * Q x i := hsm
  refine ⟨{ one_smul := fun x => inj (funext fun i => by simp [hs])
            mul_smul := fun c d x => inj (funext fun i => by simp [hs, _root_.mul_assoc])
            smul_zero := fun c => inj (funext fun i => by simp [hs])
            smul_add := fun c x y => inj (funext fun i => by simp [hs, mul_add])
            add_smul := fun c d x => inj (funext fun i => by simp [hs, add_mul])
            zero_smul := fun x => inj (funext fun i => by simp [hs]) }, hs⟩

theorem exists_period : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)), a w = H.w0 → a w' = H.bar H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → PELClass D a bas ρ em t → ∃ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) ∧ IsPeriod D' ty Q ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro l1 l2 l3 l4 E _ _ _ H D o _ g k J b em w w' a bas ρ ty t hw hw' hρ hty hP
  obtain ⟨La, _, EF, lam, ac, Q₀, Hm₀, hbij, hpol, -, u, χ, hAH, hΛ, hχ, hpt, hac⟩ :=
    _root_.GlobalTheory.PrimUnif.exists_unif_of_prim l1 l2 l3 l4 o g k J b em w w' t ((_root_.GlobalTheory.pelClass_prim_and_iso E H D o g k J b em w w' a bas ρ t hP).1 hw hw')
  obtain ⟨act, haj, hdet, hadj, I, hζ, hev⟩ := exists_act hP
  change OAct (𝓞 E) t.A at act
  rw [hρ] at hdet
  obtain ⟨h, hh⟩ : ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ (c : 𝓞 E) z,
      u.ex (h (fun i => ty i (c : E) * z i)) = u.ex (h z) ≫ act.act c :=
    _root_.GlobalTheory.exists_diagonal_coordinates_of_detCond l1 l2 l3 l4 E H D t.pol u Hm₀ χ act ty hAH hty hdet
  obtain ⟨inj, disc, span, herm, pos, him⟩ := id hpol
  let F : 𝓞 E → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) := fun c =>
    h.toLinearMap ∘ₗ (LinearMap.pi fun i => ty i (c : E) • LinearMap.proj i) ∘ₗ h.symm.toLinearMap
  have hF₀ : ∀ c z, F c z = h fun i => ty i (c : E) * h.symm z i := fun c z => rfl
  have hF : ∀ c z, u.ex (F c z) = u.ex z ≫ act.act c := fun c z => by
    have := hh c (h.symm z)
    rw [h.apply_symm_apply] at this
    exact this
  let Q₁ : La →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp Q₀
  have hQ₁ : ∀ x, h (Q₁ x) = Q₀ x := fun x => h.apply_symm_apply _
  obtain ⟨Hm₁, inj₁, disc₁, span₁, herm₁, pos₁, him₁⟩ :=
    exists_coord Q₀ Hm₀ h (AddEquiv.refl _) Q₁ hQ₁ inj disc span herm pos
  obtain ⟨_, hs⟩ := exists_module (fun i => (ty i).comp (algebraMap (𝓞 E) E)) Q₁ inj₁ (fun c x => by
    haveI := act.hom c
    have h1 : u.ex (Q₀ x) = 1 := (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩)
    have h2 : u.ex (F c (Q₀ x)) = 1 := by
      rw [hF, h1]
      exact MonObj.one_comp _
    obtain ⟨y, hy⟩ := (hΛ _).1 ((u.ker _).1 h2)
    refine ⟨y, fun i => ?_⟩
    show h.symm (Q₀ y) i = _
    rw [hy, hF₀, h.symm_apply_apply]
    rfl)
  have hs₀ : ∀ c x, Q₀ (c • x) = F c (Q₀ x) := fun c x => by
    rw [← hQ₁, hF₀]
    exact congrArg h (funext fun i => hs c x i)
  have adj : ∀ (c : 𝓞 E) x y, EF (c • x) y = EF x (H.bar c • y) := fun c x y => by
    have := (_root_.GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm l1 l2 l3 l4 t.pol u Hm₀ χ _ _ (F c) (F (H.bar c)) hAH (act.hom _) (act.hom _)
      (hF c) (hF _)).1 (hadj c) (Q₀ x) (Q₀ y)
    have h2 : ((EF (c • x) y : ℤ) : ℝ) = EF x (H.bar c • y) := by
      rw [← him, ← him, hs₀, hs₀]
      exact congrArg Complex.im this
    exact_mod_cast h2
  obtain ⟨D', e, hp, hq, hEF⟩ := GlobalTheory.PeriodDatum.exists_datum E H La EF D.p D.q g ty Q₁ Hm₁ hty hbij adj hs inj₁
    disc₁ span₁ herm₁ pos₁ (fun x y => by rw [him₁]; exact him x y)
  let Q₂ : D'.La →+ (Fin g → ℂ) := Q₀.comp e.toLinearMap.toAddMonoidHom
  have hQ₂ : ∀ x, Q₂ x = Q₀ (e x) := fun x => rfl
  obtain ⟨f, ν, hgen, hf⟩ := _root_.GlobalTheory.TorsionGenus.period_lattice_in_genus l1 l2 l3 l4 E H D D' t.pol u Hm₀ χ act Q₂ hp hq hAH
    (inj.comp e.injective)
    (fun z => (hΛ z).trans ⟨fun ⟨x, hx⟩ => ⟨e.symm x, (congrArg Q₀ (e.apply_symm_apply x)).trans hx⟩,
      fun ⟨x, hx⟩ => ⟨e x, hx⟩⟩)
    (fun x y => by rw [hEF]; exact him _ _)
    (fun c n x => by
      have := hF c ((n : ℂ)⁻¹ • Q₀ (e x))
      rw [map_smul, ← hs₀, ← map_smul e] at this
      exact this) I
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  obtain ⟨hζ', hev'⟩ := hf k (Nat.pos_of_ne_zero (Nat.cast_ne_zero.1 hk))
  let Q : D'.La →+ (Fin g → ℂ) := Q₁.comp e.toLinearMap.toAddMonoidHom
  obtain ⟨Hm, inj', disc', span', herm', pos', him'⟩ :=
    exists_coord Q₀ Hm₀ h e.toAddEquiv Q (fun x => hQ₁ _) inj disc span herm pos
  have him'' : ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y := fun x y => by
    rw [him', hEF]; exact him _ _
  refine ⟨D', f, ν, Q, Hm, hgen, hζ.symm.trans hζ', ⟨fun c x i => ?_, inj', disc', span', Hm, herm', pos', him''⟩,
    ⟨inj', disc', span', herm', pos', him''⟩, ?_⟩
  · show Q₁ (e (c • x)) i = _ * Q₁ (e x) i
    rw [map_smul]
    exact hs _ _ _
  · refine _root_.GlobalTheory.UnifTransport.transport_uniformisation o g k J b em w w' t La EF lam ac Q₀ Hm₀ D'.La D'.EF
      (fun i => f k (bas (Pi.single i 1))) (fun j x => a j • x) Q Hm e.symm.toAddEquiv h.symm hpol
      ⟨inj', disc', span', herm', pos', him''⟩ (fun x => ?_) (fun x y => ?_) (fun j x => ?_) (fun i => ?_)
      ⟨u, χ, hAH, hΛ, hχ, hpt, hac⟩
    · show Q₁ (e (e.symm x)) = _
      rw [e.apply_symm_apply]
      rfl
    · show D'.EF (e.symm x) (e.symm y) = _
      rw [hEF, e.apply_symm_apply, e.apply_symm_apply]
    · show e.symm (ac j x) = a j • e.symm x
      rw [← map_smul]
      congr 1
      obtain ⟨G, hG, hG'⟩ := hac j
      haveI := u.discrete
      have h0 := linear_eq_zero_of_mem_discrete u.Λ (G - F (a j))
        (fun z => sub_mem_of_ex_eq u (by rw [hG', hF, haj])) (Q₀ x)
      apply inj
      rw [hs₀, ← hG]
      exact sub_eq_zero.1 h0
    · have h1 : u.ex ((k : ℂ)⁻¹ • Q₀ (lam i)) = u.ex ((k : ℂ)⁻¹ • Q₂ (f k (bas (Pi.single i 1)))) :=
        Over.OverMorphism.ext ((hpt i).symm.trans ((hev i).symm.trans (hev' _)))
      obtain ⟨y, hy⟩ := (hΛ _).1 (sub_mem_of_ex_eq u h1)
      refine ⟨e.symm y, e.injective (inj ?_)⟩
      show Q₀ (e (e.symm (lam i))) = Q₀ (e (f k (bas (Pi.single i 1)) + k • e.symm y))
      rw [e.apply_symm_apply, map_add (f := _), map_nsmul, e.apply_symm_apply, map_add (f := _), map_nsmul, hy, hQ₂, ← smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk, one_smul]
      abel

end GlobalTheory.PELPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolFamOfGrpFam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

theorem torsBasis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  haveI : NeZero k := ⟨hk⟩
  have red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i := fun e =>
    Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]
  have tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1 := fun e => by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l] := by
    intro e e' he i
    have := (h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l)))
      (red e) ((red e').trans he.symm)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)
  obtain ⟨c, hc, -⟩ := h z (by rw [pow_mul, hz, one_pow])
  have hd : ∀ i, l ∣ (c i).val := fun i => by
    have := inj (fun i => k * (c i).val) (fun _ => 0) (by
      simp only [pow_zero, Finset.prod_const_one]
      rw [← hz, ← hc, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)
  choose d hd using hd
  refine ⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩
  · rw [← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]
  · have := inj (fun i => l * (c' i).val) (fun i => l * d i) (by
      simp only [pow_mul, ← hd]
      rw [hc, ← hc']) i
    rw [mul_comm k l] at this
    have h2 := Nat.ModEq.mul_left_cancel' hl this
    rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]

variable {S : Scheme.{0}}

theorem torsBasis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact torsBasis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

theorem exists_polFam_of_grpFam : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)), N' ≠ 0 → Odd m → m ∣ N' → DenseP (objPrimes b Mat κ β v) → GrpFam b Mat κ β v m A L act Q → ∃ L' : LB A.left, PolFam b Mat κ β v A L' act Q := by
  intro hL hL2 o _ g N' J b Mat κ R _ _ _ β v m A _ L act Q hN0 hodd ⟨l, hl⟩ hD ⟨hab, hsm, hlb, hamp, hlab, hfib⟩
  have hun : IsUnit (m : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, isUnit_pow_iff two_ne_zero, hl, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have := hab.comm
  obtain ⟨L', l1, l2, l3, l4, l5⟩ := GlobalTheory.OddDescent.exists_descended hL hL2 R A g m L
    (fun i => (Q i ^ l : Out.baseOver (Sp R) ⟶ A)) hab hsm hodd hun hlb hamp
    (fun i => by
      have e : l * m = N' := by rw [mul_comm, ← hl]
      have : (Q i ^ l) ^ m = 1 := by rw [← pow_mul, e, hlab.2.1]
      exact this)
    (fun K _ _ x => torsBasis_pow_linComb hl hN0 _ _ hlab.2.1 (hlab.2.2 K x))
    (fun r hr => hD r fun q hq hqp => hr q (by
      obtain ⟨K, _, _, x, s, t, hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨ψ, hψ, hi⟩ := hfib K x s t ht
      exact ⟨K, inferInstance, inferInstance, x, t.pol, ψ, hx, hψ.1, hi⟩) hqp)
  refine ⟨L', hab, hsm, l1, l2, l3, l4, hlab, fun K _ _ x s t ht => ?_⟩
  obtain ⟨ψ, hψ, hi⟩ := hfib K x s t ht
  exact ⟨ψ, hψ, l5 K x t.pol ψ hψ.1 hi⟩

end GlobalTheory.ZM.NearBuild
end


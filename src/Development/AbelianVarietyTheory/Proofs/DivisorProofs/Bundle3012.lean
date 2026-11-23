module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2991
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupExtendsNormalAffineChartAfterRescaling
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapFixingDescendedPointsSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AutLift

theorem spMap_fix (K : Type) [Field K] (k₀ : Subfield K) (σ : K ≃+* K) (h : ∀ a ∈ k₀, σ a = a) :
    spMap (σ : K →+* K) ≫ spMap k₀.subtype = spMap k₀.subtype := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact h x x.2

theorem eta_nsmul {S : Scheme.{0}} {G : Over S} [GrpObj G] {La : Type} [AddCommGroup La] (f : La → (𝟙_ (Over S) ⟶ G))
    (hf : ∀ a c, f (a + c) = f a * f c) (n : ℕ) (a : La) : f (n • a) = f a ^ n := by
  have h0 : f 0 = 1 := by
    have := hf 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem exists_objMap_fixing_descended_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} {Bb : Type} [CommRing Bb] {b : Base l Bb} (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ {s : Sp K ⟶ Sp Bb} (o : Obj D l b s) (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (π : o.t.G.left ⟶ B₀.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback o.t.G B₀ (spMap k₀.subtype) π → LBIso o.t.PP.L (M₀.pull π) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∃ n : ObjMap o o (spMap (σ : K →+* K)), ∀ x : Sp K ⟶ o.t.G.left, x ≫ o.t.G.hom = 𝟙 _ → (∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀) → x ≫ n.toSABMap.φ = spMap (σ : K →+* K) ≫ x := by
  intro E _ _ _ H D l Bb _ b K _ _ _ k₀ hk₀ s o B₀ _ _ M₀ π hB₀ hM₀ hpb hL σ hσ
  haveI : IsAlgClosed k₀ := hk₀
  have hfix := spMap_fix K k₀ σ hσ
  let st : o.t.G.left ⟶ o.t.G.left := hpb.1.lift π (o.t.G.hom ≫ spMap (σ : K →+* K))
    (by rw [hpb.1.w, Category.assoc, hfix])
  have hst₁ : st ≫ π = π := hpb.1.lift_fst _ _ _
  have hst₂ : st ≫ o.t.G.hom = o.t.G.hom ≫ spMap (σ : K →+* K) := hpb.1.lift_snd _ _ _

  have hpt : ∀ x : Sp K ⟶ o.t.G.left, x ≫ o.t.G.hom = 𝟙 _ →
      (∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀) → x ≫ st = spMap (σ : K →+* K) ≫ x := by
    rintro x hx ⟨x₀, hx₀⟩
    apply hpb.1.hom_ext
    · rw [Category.assoc, hst₁, Category.assoc, hx₀, ← Category.assoc, hfix]
    · rw [Category.assoc, hst₂, ← Category.assoc, hx, Category.assoc, hx, Category.id_comp, Category.comp_id]

  have hcart : IsGrpPullback o.t.G o.t.G (spMap (σ : K →+* K)) st :=
    hpb.cancel (hpb.congr hfix.symm hst₁.symm) hst₂

  have hact : ∀ a, (o.t.act.act a).left ≫ st = st ≫ (o.t.act.act a).left := by
    intro a
    obtain ⟨f₀, -, hf₀⟩ := GlobalTheory.AlgClosedHomDescent.hom_descends k₀ K k₀.subtype B₀ B₀ o.t.G o.t.G π π hB₀ hB₀ hpb hpb
      (o.t.act.act a) (o.t.act.hom a)
    apply hpb.1.hom_ext
    · rw [Category.assoc, hst₁, Category.assoc, ← hf₀, ← Category.assoc, hst₁, hf₀]
    · rw [Category.assoc, hst₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hst₂]

  have hLB : LBIso o.t.PP.L (o.t.PP.L.pull st) := by
    have h1 : LBIso (o.t.PP.L.pull st) (M₀.pull π) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.t.PP.L st st rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame M₀ _ (fun _ => π) _ st fun _ => hst₁.symm) hL
    exact LBIso.trans o.t.PP.isLB (pull_isLB hM₀ π) (pull_isLB o.t.PP.isLB st) hL (LBIso.symm h1)

  obtain ⟨m, hm⟩ := _root_.GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper o.t o.t (spMap (σ : K →+* K)) st o.proper hcart hact hLB
  have hφ : m.cm.F = st := hm

  have hun : η[o.t.G].left ≫ π = spMap k₀.subtype ≫ η[B₀].left := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hpb
  have htor : ∀ (y : 𝟙_ (Over (Sp K)) ⟶ o.t.G) (n : ℕ), 0 < n → y ^ n = 1 →
      y.left ≫ st = spMap (σ : K →+* K) ≫ y.left := by
    intro y n hn hy
    obtain ⟨y₀, hy₀⟩ := _root_.GlobalTheory.AlgClosedDescent.grpPullback_point_descends K k₀ hk₀ B₀ o.t.G π hB₀ hpb n hn y η[B₀].left (by
      rw [hy, ← hun]; simp [Hom.one_def])
    refine hpt y.left ?_ ⟨y₀, hy₀⟩
    simpa using Over.w y
  have hMmem : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_left : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) this
  refine ⟨{ m with
    eta := fun a => by
      rw [hφ]
      refine htor (o.eta a) l.M (by have := l.three_le; omega) ?_
      rw [← eta_nsmul o.eta o.eta_add, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact o.eta_ker _ (Submodule.smul_mem_smul hMmem trivial)
    etaA := fun a => by
      rw [hφ]
      refine htor (o.etaA a) l.A l.A_pos ?_
      rw [← eta_nsmul o.etaA o.etaA_add]
      exact o.etaA_ker a }, fun x hx hx₀ => ?_⟩
  show x ≫ m.cm.F = _
  rw [hφ]
  exact hpt x hx hx₀

end GlobalTheory.AutLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfNeConj
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_not_and_not_of_sub_closed {A : Type} [AddCommGroup A] (P Q : A → Prop)
    (hP : ∀ a b, P a → P b → P (a - b)) (hQ : ∀ a b, Q a → Q b → Q (a - b)) {a b : A} (ha : ¬ P a) (hb : ¬ Q b) :
    ∃ c, ¬ P c ∧ ¬ Q c := by
  by_cases h1 : Q a
  · by_cases h2 : P b
    · refine ⟨a + b, fun h => ha ?_, fun h => hb ?_⟩
      · simpa using hP _ _ h h2
      · simpa using hQ _ _ h h1
    · exact ⟨b, h2, hb⟩
  · exact ⟨a, ha, h1⟩

theorem mem_map_bar_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔭 : Ideal (𝓞 E)) (x : 𝓞 E) :
    x ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ↔ H.bar x ∈ 𝔭 := by
  rw [Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) (fun a => ⟨H.bar a, bar_bar H a⟩)]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have := bar_bar H a
    simpa [this] using ha
  · exact fun hx => ⟨_, hx, bar_bar H x⟩

theorem mem_of_smul_mem_of_not_mem {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {I : Ideal O}
    (hI : I.IsMaximal) (N : Submodule O X) {c : O} (hc : c ∉ I) {x : X} (hx : c • x ∈ N ⊔ I • (⊤ : Submodule O X)) :
    x ∈ N ⊔ I • (⊤ : Submodule O X) := by
  obtain ⟨d, i, hi, hd⟩ := hI.exists_inv hc
  have : x = d • (c • x) + i • x := by rw [smul_smul, ← add_smul, hd, one_smul]
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ hx) (Submodule.mem_sup_right (Submodule.smul_mem_smul hi trivial))

theorem exists_improves_of_ne_conj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (e' : 𝓞 E) (he1' : e' - 1 ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (he' : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) → e' ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (v₂ : Z') (hv₂ : y v₂ ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) X)) (ℓ₁ : Z' →ₗ[𝓞 E] 𝓞 E)
    (hℓ₁ : ℓ₁ v₂ ∉ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  intro E _ _ _ H D X _ _ y n Z Z' h 𝔭 h𝔭 hn𝔭 hb e he1 he e' he1' he' v hv ℓ₀ hℓ₀ v₂ hv₂ ℓ₁ hℓ₁ θ hθ s hs hs' hgen hZ
  set 𝔭' := 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) with h𝔭'def
  have hmem : ∀ x, x ∈ 𝔭' ↔ H.bar x ∈ 𝔭 := mem_map_bar_iff H 𝔭
  have h𝔭' : 𝔭'.IsMaximal := by
    have : 𝔭' = 𝔭.comap (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.ext fun x => hmem x
    rw [this]
    exact Ideal.comap_isMaximal_of_surjective _ (fun a => ⟨H.bar a, bar_bar H a⟩)
  have hn' : (n : 𝓞 E) ∈ 𝔭' := (hmem _).2 (by simpa using hn𝔭)
  obtain ⟨ζ, hζZ, hζ, hζs, hopp⟩ := h.exists_rank_one (m := 0) (zero_mem _) θ (fun t => by simp [hθ])
  have himg : ∀ I : Ideal (𝓞 E), img D y Z' I = LinearMap.range (y ∘ₗ Z'.subtype) ⊔ I • ⊤ := fun I => by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have himg' : ∀ (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (I : Ideal (𝓞 E)),
      img D y (LinearMap.range (Z'.subtype + ℓ.smulRight (0 + ζ ℓ))) I =
        LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y (ζ ℓ))) ⊔ I • ⊤ := fun ℓ I => by
    have : y ∘ₗ Z'.subtype + ℓ.smulRight (y (ζ ℓ)) = y ∘ₗ (Z'.subtype + ℓ.smulRight (0 + ζ ℓ)) := by
      ext x; simp
    rw [this, LinearMap.range_comp]

  obtain ⟨ℓ₂, hℓ₂⟩ : ∃ ℓ₂, y (ζ ℓ₂) ∉ img D y Z' 𝔭 := by
    obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := SetLike.not_le_iff_exists.1 hZ
    obtain ⟨ℓ, hℓ⟩ := GlobalTheory.LowFilt.exists_linear_theta_factor D Z' θ s (fun h0 => hs (h0 ▸ zero_mem _)) hgen z
    have h0 : ζ ℓ - H.bar s • z = 0 := h.symm.eq_zero (sub_mem (hζZ ℓ) (Z.smul_mem _ hz)) fun x hx => by
      rw [ef_swap, map_sub, hζ ℓ ⟨x, hx⟩, hℓ ⟨x, hx⟩]; simp
    refine ⟨ℓ, fun hh => hz' ?_⟩
    rw [sub_eq_zero.1 h0, map_smul] at hh
    exact mem_of_smul_mem_of_not_mem h𝔭 _ hs' hh
  obtain ⟨ℓ', h1, h2⟩ := exists_not_and_not_of_sub_closed (fun ℓ : Z' →ₗ[𝓞 E] 𝓞 E => ℓ v₂ ∈ 𝔭')
    (fun ℓ => y (ζ ℓ) ∈ img D y Z' 𝔭) (fun a b ha hb => sub_mem ha hb)
    (fun a b ha hb => by simpa only [map_sub] using sub_mem ha hb) hℓ₁ hℓ₂
  have he𝔭' : e ∈ 𝔭' := he _ h𝔭' hn' hb
  have he'𝔭 : e' ∈ 𝔭 := he' _ h𝔭 hn𝔭 hb.symm
  set ℓ := e • ℓ₀ + e' • ℓ' with hℓdef
  have hℓx : ∀ x, ℓ x = e * ℓ₀ x + e' * ℓ' x := fun x => rfl
  have hv𝔭 : ℓ v ∉ 𝔭 := fun hh => hℓ₀ (by
    have : ℓ₀ v = ℓ v - (e - 1) * ℓ₀ v - e' * ℓ' v := by rw [hℓx]; ring
    rw [this]
    exact sub_mem (sub_mem hh (𝔭.mul_mem_right _ he1)) (𝔭.mul_mem_right _ he'𝔭))
  have hv𝔭' : ℓ v₂ ∉ 𝔭' := fun hh => h1 (by
    have : ℓ' v₂ = ℓ v₂ - (e' - 1) * ℓ' v₂ - e * ℓ₀ v₂ := by rw [hℓx]; ring
    show ℓ' v₂ ∈ 𝔭'
    rw [this]
    exact sub_mem (sub_mem hh (𝔭'.mul_mem_right _ he1')) (𝔭'.mul_mem_right _ he𝔭'))
  have k𝔭 := range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (ζ ℓ)) 𝔭 h𝔭 (v := v) hv hv𝔭
  have k𝔭' := range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (ζ ℓ)) 𝔭' h𝔭' (v := v₂) hv₂ hv𝔭'
  refine ⟨_, hopp ℓ, fun 𝔮 h𝔮 hn𝔮 => ?_, fun hle => h2 ?_⟩
  · rw [himg, himg']
    by_cases q1 : 𝔮 = 𝔭
    · rw [q1]; exact k𝔭.2
    by_cases q2 : 𝔮 = 𝔭'
    · rw [q2]; exact k𝔭'.2
    exact range_le_of_mem _ _ _ _ fun x => by
      rw [hℓx]
      exact add_mem (𝔮.mul_mem_right _ (he _ h𝔮 hn𝔮 q1)) (𝔮.mul_mem_right _ (he' _ h𝔮 hn𝔮 q2))
  · rw [himg'] at hle
    have hu := hle k𝔭.1
    have b1 : H.bar e ∈ 𝔭 := (hmem _).1 he𝔭'
    have b2 : H.bar e' - 1 ∈ 𝔭 := by simpa using (hmem _).1 he1'
    have : y (ζ ℓ') = y (ζ ℓ) - H.bar e • y (ζ ℓ₀) - (H.bar e' - 1) • y (ζ ℓ') := by
      rw [hℓdef, map_add (f := _), hζs, hζs, map_add (f := _), map_smul, map_smul, sub_smul, one_smul]; abel
    show y (ζ ℓ') ∈ img D y Z' 𝔭
    rw [this]
    exact sub_mem (sub_mem hu (Submodule.mem_sup_right (Submodule.smul_mem_smul b1 trivial)))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul b2 trivial))

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankOneChangeImprovesImageRealPrime
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem mem_of_smul_mem_sup {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {I : Ideal O} (hI : I.IsMaximal)
    {N : Submodule O X} (hN : I • (⊤ : Submodule O X) ≤ N) {a : O} (ha : a ∉ I) {u : X} (hu : a • u ∈ N) : u ∈ N := by
  obtain ⟨c, i, hi, hc⟩ := hI.exists_inv ha
  have : c • (a • u) + i • u = u := by rw [smul_smul, ← add_smul, hc, one_smul]
  rw [← this]
  exact add_mem (N.smul_mem c hu) (hN (Submodule.smul_mem_smul hi trivial))

theorem map_range_rank_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (Z' : Submodule (𝓞 E) D.La)
    (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (u : D.La) :
    (LinearMap.range (Z'.subtype + ℓ.smulRight u)).map y = LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y u)) := by
  rw [← LinearMap.range_comp]
  congr 1
  ext x
  simp

end GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_improves_of_real {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭) :
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  have hm : (0 : D.La) ∈ perp D Z ⊓ perp D Z' := zero_mem _
  obtain ⟨ζ, hζZ, hζ, hζs, hopp⟩ := h.exists_rank_one hm θ (fun t => by simp [hθ])
  have hN : 𝔭 • (⊤ : Submodule (𝓞 E) X) ≤ img D y Z' 𝔭 := le_sup_right

  set P1 : (Z' →ₗ[𝓞 E] 𝓞 E) → Prop := fun ℓ => ℓ v ∈ 𝔭 with hP1
  set P2 : (Z' →ₗ[𝓞 E] 𝓞 E) → Prop := fun ℓ => y (ζ ℓ) ∈ img D y Z' 𝔭 with hP2
  have P1sub : ∀ a b, P1 (a + b) → P1 b → P1 a := fun a b hab hb' => by
    have := sub_mem hab hb'
    simpa [hP1] using this
  have P2sub : ∀ a b, P2 (a + b) → P2 b → P2 a := fun a b hab hb' => by
    have := sub_mem hab hb'
    simpa [hP2, map_add (f := _)] using this

  obtain ⟨x, ⟨z, hz, rfl⟩, hx⟩ := Set.not_subset.1 hZ
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ 𝔭.zero_mem)
  obtain ⟨ℓ₂, hℓ₂⟩ := _root_.GlobalTheory.LowFilt.exists_linear_theta_factor D Z' θ s hs0 hgen z
  have hζ₂ : ζ ℓ₂ = H.bar s • z := by
    obtain ⟨c, -, hu⟩ := h.symm.2.2.1 (θ.comp ℓ₂.toAddMonoidHom)
    have e1 := hu ⟨ζ ℓ₂, hζZ ℓ₂⟩ fun a => by simpa using hζ ℓ₂ a
    have e2 := hu ⟨H.bar s • z, Z.smul_mem _ hz⟩ fun a => by simpa using (hℓ₂ a).symm
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hℓ₂P : ¬ P2 ℓ₂ := fun hP => by
    simp only [hP2, hζ₂, map_smul] at hP
    exact hx (mem_of_smul_mem_sup h𝔭 hN hs' hP)

  obtain ⟨ℓ₁, h1, h2⟩ : ∃ ℓ₁, ¬ P1 ℓ₁ ∧ ¬ P2 ℓ₁ := by
    by_cases ha : P2 ℓ₀
    · by_cases hb1 : P1 ℓ₂
      · refine ⟨ℓ₀ + ℓ₂, fun hp => hℓ₀ (P1sub _ _ hp hb1), fun hp => hℓ₂P ?_⟩
        rw [add_comm] at hp
        exact P2sub _ _ hp ha
      · exact ⟨ℓ₂, hb1, hℓ₂P⟩
    · exact ⟨ℓ₀, hℓ₀, ha⟩
  have he𝔭 : e ∉ 𝔭 := fun hm' => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem hm' he1
    simpa using this))
  have hbe : H.bar e ∉ 𝔭 := fun hm' => he𝔭 (by
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hm'
    rw [hb] at this
    simpa [bar_bar] using this)
  set ℓ := e • ℓ₁ with hℓ
  refine ⟨LinearMap.range (Z'.subtype + ℓ.smulRight (0 + ζ ℓ)), hopp ℓ, fun 𝔮 h𝔮 hn𝔮 => ?_, fun hle => ?_⟩
  · have hZ'm : Z'.map y = LinearMap.range (y ∘ₗ Z'.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    show Z'.map y ⊔ _ ≤ _ ⊔ _
    rw [map_range_rank_one, hZ'm]
    by_cases hq : 𝔮 = 𝔭
    · subst hq
      refine (range_le_of_ker _ ℓ _ 𝔮 h𝔮 (v := v) (by simpa using hv) ?_).2
      show e * ℓ₁ v ∉ 𝔮
      exact fun hm' => h1 ((h𝔮.isPrime.mem_or_mem hm').resolve_left he𝔭)
    · exact range_le_of_mem _ ℓ _ 𝔮 fun x => by
        show e * ℓ₁ x ∈ 𝔮
        exact Ideal.mul_mem_right _ _ (he 𝔮 h𝔮 hn𝔮 hq)
  · have hZ'm : Z'.map y = LinearMap.range (y ∘ₗ Z'.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hmem := (range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (0 + ζ ℓ)) 𝔭 h𝔭 (v := v) (by simpa using hv)
      (show e * ℓ₁ v ∉ 𝔭 from fun hm' => h1 ((h𝔭.isPrime.mem_or_mem hm').resolve_left he𝔭))).1
    have hin : y (ζ ℓ) ∈ img D y Z' 𝔭 := by
      apply hle
      show _ ∈ _ ⊔ _
      rw [map_range_rank_one]
      simpa using hmem
    rw [hℓ, hζs, map_smul] at hin
    exact h2 (mem_of_smul_mem_sup h𝔭 hN hbe hin)

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRechartingThetaSystemAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.UPoinc.exists_rechart_wit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w₀ ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ ∧ ∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (ρ'.pt x).left := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi w₀ hw₀
  obtain ⟨⟨hL, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  obtain ⟨U₀, u₀, hU₀a, hwU₀, hu₀⟩ := GlobalTheory.UPoinc.ChartAt.exists_affine_chart_ratHull_lift E H Dw hpq l Xo cf C X w₀ hw₀
  obtain ⟨U₁, h₁, P₁, hU₁₀, hU₁a, hwU₁, hP₁⟩ := GlobalTheory.UPoinc.USetup.exists_polAV_ringOn_near E H Dw hpq l Xo cf C X w₀ hw₀ U₀ u₀ hU₀a hwU₀ hu₀
  have hN : 1 ≤ X.S.N := by have := X.S.N_ge; omega
  obtain ⟨U, h, P', φ, hUU₁, hUa, hwU, hφ, hφL, _hgφ, ⟨th, hth⟩, b, hb⟩ :=
    GlobalTheory.Poinc.exists_univBasis_affineChart X.o₁ X.Ω₁ X.M U₁ w₀ hU₁a hwU₁ P₁ X.S.N hN
  let u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf := spMap (Subalgebra.inclusion (ratHull_mono (h₁.trans h))).toRingHom ≫ u₀
  have hu' : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hUO : UOver Xo cf P' (toRat (X.M.ringOn U)) u' := by
    refine (uOver_baseChange_iff hφ hφL (toRat (X.M.ringOn U))).2 ?_
    have h2 := hP₁.comp (Subalgebra.inclusion (ratHull_mono h)).toRingHom
    have e1 : (Subalgebra.inclusion (ratHull_mono h)).toRingHom.comp (toRat (X.M.ringOn U₁)) =
        (toRat (X.M.ringOn U)).comp (Subalgebra.inclusion h).toRingHom := RingHom.ext fun _ => rfl
    have e2 : spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫
        spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom ≫ u₀ = u' := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    rw [e1, e2] at h2
    exact h2
  obtain ⟨G, _, α, β, hα, hβ, hLG⟩ := hUO
  have wβ : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom) ≫ u' ≫ pullback.fst _ _ := by
    rw [wi.hβ.1.w, ← hu']
    simp only [Category.assoc]
  let m : wi.G.left ⟶ G.left := hβ.1.lift wi.β (wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom) wβ
  have hm₁ : m ≫ β = wi.β := hβ.1.lift_fst _ _ _
  have hm₂ : m ≫ G.hom = wi.G.hom ≫ spMap (ratHull (X.M.ringOn U)).val.toRingHom := hβ.1.lift_snd _ _ _
  have hm : IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m :=
    hβ.cancel (wi.hβ.congr (by rw [← hu']; simp only [Category.assoc]) hm₁.symm) hm₂
  have hmα : IsGrpPullback wi.G P'.A (spMap (X.M.ringOn U).val.toRingHom) (m ≫ α) :=
    (hm.comp hα).congr (spMap_val_toRat (X.M.ringOn U)) rfl
  have hLU := Xo.univ.t.PP.isLB
  have hLρ := X.ρ.P.isLB
  have hLP := P'.isLB
  have hLw : LBIso (X.ρ.P.L.pull wi.α) (P'.L.pull (m ≫ α)) :=
    LBIso.trans (pull_isLB hLρ _) (pull_isLB hLU _) (pull_isLB hLP _) wi.hL
      (LBIso.trans (pull_isLB hLU _) (pull_isLB (pull_isLB hLU _) _) (pull_isLB hLP _)
        (GenSpread.lbIso_pull_pull hLU m hm₁.symm)
        (LBIso.trans (pull_isLB (pull_isLB hLU _) _) (pull_isLB (pull_isLB hLP _) _) (pull_isLB hLP _)
          (GenSpread.lbIso_pullback hLG.symm m) (GenSpread.lbIso_pull_pull hLP m rfl).symm))
  obtain ⟨P₀, a, a', e, he, hea, hea', ha, ha', hl, hl'⟩ :=
    GlobalTheory.UPoinc.exists_polAV_common_pullback X.Ω₁ (Sp X.S.R) (Sp (X.M.ringOn U)) X.ρ.P P' (spMap X.S.R.val.toRingHom) (spMap (X.M.ringOn U).val.toRingHom) wi.G wi.α (m ≫ α)
      wi.hα hmα hLw
  have hne : ((U : Set X.M.Z)).Nonempty := ⟨w₀, hwU⟩
  have hyp : HypS P'.A P'.L :=
    GlobalTheory.Poinc.hypS_of_generic_ringOn X.o₁ X.Ω₁ X.M U hUa hne X.normal X.S.R X.ρ.P P' P₀ _ a a' ha ha' hl hl' X.ρ.hypS
  have hg : P'.g = X.S.g :=
    (GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ P' P₀ _ a' ha').symm.trans
      ((GlobalTheory.polAV_g_eq_of_isGrpPullback X.Ω₁ _ X.ρ.P P₀ _ a ha).trans X.ρ.g_eq)
  have fg : (X.M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ X.M U hUa hne
  have frac : ∀ x : X.Ω₁, ∃ a ∈ (X.M.ringOn U), ∃ b ∈ (X.M.ringOn U), x = a / b := fun x => by
    obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hUa hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  haveI := RatModel.isFractionRing_ringOn hUa hne
  haveI : IsIntegrallyClosed (X.M.ringOn U) :=
    TorsExtend.isIntegrallyClosed_ringOn X.M ((isNormalScheme_iff_pred _).1 X.normal) hUa hne
  haveI := ArithBase.ded (o := X.o₁) (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.ringOn U) := isNoetherianRing_of_fg fg
  have hn : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (le_trans one_le_two X.S.N_ge)
  have hu : IsUnit ((X.S.r * X.S.N : ℕ) : (X.M.ringOn U)) := by
    have := X.S.unit.map (algebraMap X.o₁ (X.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', hadd, hbij, h₃, hw0⟩ := TorsExtend.exists_labelled hL X.S.R.val.toRingHom X.ρ.P P' P₀ a a' ha ha' hl hl' hn hu
    (M := X.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X.ρ.pt X.ρ.pt_add X.ρ.pt_bij
  have hweil : ∀ x y (c : (X.M.ringOn U)ˣ), (c : (X.M.ringOn U)) = algebraMap X.o₁ (X.M.ringOn U) (X.S.ζ ^ (X.S.r * X.S.N * (eStd X.S.g _ x y).val)) →
      WeilIs P'.A P'.L (X.S.r * X.S.N : ℕ) (pt' x) (pt' y) (unitOn c) := fun x y c hc => by
    obtain ⟨c₀, hc₀⟩ := ((X.S.prim.isUnit (by positivity)).pow (X.S.r * X.S.N * (eStd X.S.g _ x y).val)).map
      (algebraMap X.o₁ X.S.R)
    refine h₃ x y c₀ c ?_ (X.ρ.weil x y c₀ hc₀)
    rw [hc₀, hc]
    rfl
  let Q : (P : PolAV (Sp (X.M.ringOn U))) → (X.S.Gam → (baseOver (Sp (X.M.ringOn U)) ⟶ P.A)) → Prop := fun P pt =>
    (∃ (P₀ : PolAV (Sp X.Ω₁)) (a : P₀.A.left ⟶ X.ρ.P.A.left) (a' : P₀.A.left ⟶ P.A.left),
      IsGrpPullback P₀.A X.ρ.P.A (spMap ((RingHom.id _).comp X.S.R.val.toRingHom)) a ∧
      IsGrpPullback P₀.A P.A (spMap (X.M.ringOn U).val.toRingHom) a' ∧ LBIso P₀.L (X.ρ.P.L.pull a) ∧ LBIso P₀.L (P.L.pull a') ∧
      ∀ x, ∃ w : Sp X.Ω₁ ⟶ P₀.A.left, w ≫ a = spMap ((RingHom.id _).comp X.S.R.val.toRingHom) ≫ (X.ρ.pt x).left ∧
        w ≫ a' = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left) ∧
    (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ P.A.left) (β : G.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback G P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧
      LBIso (P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧
      ∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧
        ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧
          w ≫ m ≫ α = spMap (X.M.ringOn U).val.toRingHom ≫ (pt x).left)
  have hQ : Q P' pt' := by
    refine ⟨⟨P₀, a, a', ha, ha', hl, hl', hw0⟩, G, inferInstance, α, β, hα, hβ, hLG, m, hm, hm₁, fun x => ?_⟩
    obtain ⟨w0, h₁, h₂⟩ := hw0 x
    refine ⟨w0 ≫ inv e, ?_, ?_⟩
    · rw [← hea, Category.assoc, IsIso.inv_hom_id_assoc, h₁]
    · rw [← hea', Category.assoc, IsIso.inv_hom_id_assoc]
      exact h₂
  obtain ⟨c₀, hc, hthm, hevm, ρ', ⟨hS₁, G', _, α', β', hα', hβ', hL', m', hm', hm₁', hpt'⟩, hi₀⟩ :=
    GlobalTheory.ThetaExtend.exists_real_rechart hL X.S X.ρ (X.M.ringOn U) fg frac P' P₀ a a' pt' th b ha ha' hl hl' hg hyp hadd hbij hweil
      hw0 hth hb Q hQ
  exact ⟨U, c₀, hc, fg, frac, hthm, hevm, ρ', u', hUa, hwU, hS₁, hi₀, hu', G', inferInstance, α', β', hα', hβ', hL', m',
    hm', hm₁', hpt'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupRegularOverModuliPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.SetupAt

theorem exists_uSetup_regular_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c), ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w :=
  GlobalTheory.UPoinc.exists_uSetup_regular_at

end GlobalTheory.UPoinc.SetupAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDefStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef : ∀ (d : ℕ), 0 < d → ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  first | (exact @GlobalTheory.ZarhinFam.zW_symm_posDef) | (exact GlobalTheory.ZarhinFam.zW_symm_posDef) | (intros; apply GlobalTheory.ZarhinFam.zW_symm_posDef  <;> assumption)
end


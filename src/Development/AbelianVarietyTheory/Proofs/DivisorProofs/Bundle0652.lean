module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0630
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamPeriodsLinear
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer


open Opposite in
theorem periods_linear : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ x y q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ y q' → IsPer u.ex u.Λ (x + y) (q + q') ∧ IsPer u.ex u.Λ (x - y) (q - q')) ∧ ∀ (a : ℂ) x q, IsPer u.ex u.Λ x q → IsPer u.ex u.Λ (a • x) (a • q) := by
  intro A _ g L u
  have hO : ∀ U : A.left.Opens, IsOpen (pre u.ex U) := fun U ↦ (u.hol U 0).1
  have vadd : ∀ (U : A.left.Opens) (b b' : Γ(A.left, U)) z, val u.ex U (b + b') z = val u.ex U b z + val u.ex U b' z :=
    fun U b b' z ↦ valAt'_add _ _ _ _
  have vsub : ∀ (U : A.left.Opens) (b b' : Γ(A.left, U)) z, val u.ex U (b - b') z = val u.ex U b z - val u.ex U b' z :=
    fun U b b' z ↦ valAt'_sub _ _ _ _
  have vsmul : ∀ (U : A.left.Opens) (a : ℂ) (b : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (a • b) z = a * val u.ex U b z := by
    intro U a b z hz
    have e : (u.ex z).left ≫ str A = 𝟙 (Sp ℂ) := by
      rw [str, Category.comp_id]; exact Over.w (u.ex z)
    have k : valAt' (u.ex z).left U ((secMap (str A) U).hom a) = a :=
      (valAt'_appLE (u.ex z).left (str A) ⊤ U le_top _ hz).trans
        ((congrArg (fun p ↦ valAt' p ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e).trans (valAt'_id_top a))
    exact (valAt'_mul (u.ex z).left U ((secMap (str A) U).hom a) b).trans (congrArg (· * val u.ex U b z) k)
  have dA : ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (U : A.left.affineOpens),
      DifferentiableOn ℂ (k U) (pre u.ex U.1) → ∀ z ∈ pre u.ex U.1, DifferentiableAt ℂ (k U) z :=
    fun k U hk z hz ↦ hk.differentiableAt ((hO _).mem_nhds hz)
  refine ⟨fun x y q q' hx hy ↦ ?_, fun a x q hx ↦ ?_⟩
  · obtain ⟨c, h, rfl, ⟨h1, h2, h3⟩, hp⟩ := hx
    obtain ⟨c', h', rfl, ⟨h1', h2', h3'⟩, hp'⟩ := hy
    constructor
    · refine ⟨c + c', fun U z ↦ h U z + h' U z, map_add _ _ _,
        ⟨fun U ↦ (h1 U).add (h1' U), fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
      · change h V z + h' V z = (h U z + h' U z) + val u.ex V.1 (c.1.1 (op U) (op V) f + c'.1.1 (op U) (op V) f) z
        refine Eq.trans ?_ (congrArg _ (vadd V.1 _ _ z).symm)
        rw [h2 U V f z hz, h2' U V f z hz]; ring
      · change fderiv ℂ (fun z ↦ h U z + h' U z) z = evForm u.ex U.1 z (c.1.2 (op U) + c'.1.2 (op U))
        rw [fderiv_fun_add (dA h U (h1 U) z hz) (dA h' U (h1' U) z hz), map_add (f := _), h3 U z hz, h3' U z hz]
      · simp only [Pi.add_apply]
        rw [hp U l z hz, hp' U l z hz]; ring
    · refine ⟨c - c', fun U z ↦ h U z - h' U z, map_sub _ _ _,
        ⟨fun U ↦ (h1 U).sub (h1' U), fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
      · change h V z - h' V z = (h U z - h' U z) + val u.ex V.1 (c.1.1 (op U) (op V) f - c'.1.1 (op U) (op V) f) z
        refine Eq.trans ?_ (congrArg _ (vsub V.1 _ _ z).symm)
        rw [h2 U V f z hz, h2' U V f z hz]; ring
      · change fderiv ℂ (fun z ↦ h U z - h' U z) z = evForm u.ex U.1 z (c.1.2 (op U) - c'.1.2 (op U))
        rw [fderiv_fun_sub (dA h U (h1 U) z hz) (dA h' U (h1' U) z hz), map_sub, h3 U z hz, h3' U z hz]
      · simp only [Pi.sub_apply]
        rw [hp U l z hz, hp' U l z hz]; ring
  · obtain ⟨c, h, rfl, ⟨h1, h2, h3⟩, hp⟩ := hx
    refine ⟨a • c, fun U z ↦ a * h U z, map_smul _ _ _,
      ⟨fun U ↦ (h1 U).const_mul a, fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
    · change a * h V z = a * h U z + val u.ex V.1 (a • c.1.1 (op U) (op V) f) z
      refine Eq.trans ?_ (congrArg _ (vsmul V.1 a _ z hz).symm)
      rw [h2 U V f z hz]; ring
    · change fderiv ℂ (fun z ↦ a * h U z) z = evForm u.ex U.1 z (a • c.1.2 (op U))
      rw [fderiv_const_mul (dA h U (h1 U) z hz), map_smul, h3 U z hz]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hp U l z hz]; ring

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCocycleAffineOpenIsCoboundary
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer


open GlobalTheory.AbLaw in
theorem cech_one_cocycle_split : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (K : Type) (W : K → X.Opens), (∀ i, W i ≤ U) → U ≤ ⨆ i, W i → ∀ f : ∀ i j, Γ(X, W i ⊓ W j), (∀ i j k, (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ⊓ W k ≤ W i ⊓ W j)).op).hom (f i j) + (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W j ⊓ W k ≤ W j ⊓ W k)).op).hom (f j k) = (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W j ⊓ W k ≤ W i ⊓ W k)).op).hom (f i k)) → ∃ a : ∀ i, Γ(X, W i), ∀ i j, f i j = (X.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op).hom (a i) - (X.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op).hom (a j) := by
  intro X U hU K W hW hc f hf
  have hM := ReciprocityTheory.ChartRestriction.G.Out.Inh.trivLB_isLB X
  obtain ⟨ψ, hψ⟩ := GlobalTheory.AbLaw.CechOne.cechHOneVanishesOnOpen_of_isAffineOpen hM hU K W hW hc
    (fun a b => (GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top).symm (f a b)) (by
      intro a b d O ha hb hd
      apply (GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top).injective
      have h : rs X inf_le_left (f a b) + rs X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (f b d) =
        rs X (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W a ⊓ W b ⊓ W d ≤ W a ⊓ W d) (f a d) := hf a b d
      have h := congrArg (rs X (le_inf (le_inf ha hb) hd)) h
      simp only [map_add (f := _), rs_rs] at h
      rw [map_add (f := _), GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
        GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
        GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top]
      simpa only [LinearEquiv.apply_symm_apply] using h)
  refine ⟨fun a => GlobalTheory.AbLaw.SecOn.chart hM PUnit.unit le_top (ψ a), fun a b => ?_⟩
  have h := (LinearEquiv.symm_apply_eq _).1 (hψ a b)
  rw [h, map_sub, GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top,
    GlobalTheory.AbLaw.SecOn.chart_restrict hM PUnit.unit le_top]

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondOntoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clopenCond_onto_alt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), ∀ g : Over.mk (x ≫ T'.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = g := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.clopenCond_onto) | (exact GlobalTheory.UPel.HT.EtLev.clopenCond_onto) | (intros; apply GlobalTheory.UPel.HT.EtLev.clopenCond_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryDegreePartCocycleModIdealStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_degree_part_cocycle_mod_ideal : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (m : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) Q), (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → In N (cob2 (up Q μ) c) → ∀ n : Fin d →₀ ℕ, n.degree = m → ∀ a b : Fin d →₀ ℕ, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → ∃ r ∈ N, (∏ i, Nat.choose ((a + b) i) (a i) : Q) * coeff (Finsupp.sumElim (a + b) (n - (a + b))) c - (∏ i, Nat.choose ((n - a) i) (b i) : Q) * coeff (Finsupp.sumElim a (n - a)) c = algebraMap B Q r := by
  first | exact @GlobalTheory.CobRel.cocycle_rel_mod | exact GlobalTheory.CobRel.cocycle_rel_mod | (intros; apply GlobalTheory.CobRel.cocycle_rel_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryFrobeniusCommuteModPQuasiLog
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobCongr

variable {Q : Type} [CommRing Q]

theorem frob_eq_expand {σ : Type} (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  rw [frob, expand, substAlgHom_apply]

theorem subst_frob {σ τ : Type} (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {a : σ → MvPowerSeries τ Q}
    (ha : HasSubst a) (g : MvPowerSeries σ Q) :
    subst a (frob p s g) = subst (fun i => a i ^ p) (map s g) := by
  rw [frob, subst_comp_subst_apply (HasSubst.X_pow hp) ha]
  congr 1
  funext i
  rw [subst_pow ha, subst_X ha]

theorem frob_subst {σ τ : Type} [Finite σ] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {a : σ → MvPowerSeries τ Q}
    (ha : HasSubst a) (g : MvPowerSeries σ Q) :
    frob p s (subst a g) = subst (fun i => expand p hp (map s (a i))) (map s g) := by
  have ha' : HasSubst fun i => map s (a i) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by
      rw [constantCoeff_map]; exact (ha.const_coeff i).map s
  rw [frob_eq_expand p hp, map_subst ha, expand_subst p hp ha']

end GlobalTheory.FrobCongr

namespace GlobalTheory.FrobCongr

theorem coeff_pow_sub_expand_mem {B τ : Type} [CommRing B] (p : ℕ) [hp : Fact p.Prime]
    (hnu : ¬IsUnit (p : B)) (σ : B →+* B) (hσ : ∀ b, (p : B) ∣ σ b - b ^ p)
    (g : MvPowerSeries τ B) (α : τ →₀ ℕ) :
    coeff α (g ^ p - expand p hp.out.ne_zero (map σ g)) ∈ Ideal.span {(p : B)} := by
  haveI : CharP (B ⧸ Ideal.span {(p : B)}) p := CharP.quotient B p hnu
  set π := Ideal.Quotient.mk (Ideal.span {(p : B)})
  have hπσ : π.comp σ = (frobenius (B ⧸ Ideal.span {(p : B)}) p).comp π := by
    ext b
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (hσ b)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map]
  change coeff α (map π (g ^ p - expand p hp.out.ne_zero (map σ g))) = 0
  rw [map_sub, map_pow, map_expand, map_map, hπσ, ← map_map, ← map_expand,
    map_frobenius_expand, sub_self, map_zero]

end GlobalTheory.FrobCongr

namespace GlobalTheory.FrobCongr

theorem dIn_comb {B Q σ ι : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype ι]
    (b : ι → B) (e : ι → MvPowerSeries σ Q) (he : ∀ i, DIn (⊤ : Ideal B) (e i)) :
    DIn (⊤ : Ideal B) (comb b e) := by
  intro α j
  choose c _ hc using fun i => he i α j
  refine ⟨∑ i, b i * c i, trivial, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, coeff_smul, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hc i]; ring

theorem dIn_map {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (φ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (φ b)) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) : DIn (⊤ : Ideal B) (map s f) := by
  intro α j
  obtain ⟨c, -, hc⟩ := hf α j
  refine ⟨φ c, trivial, ?_⟩
  rw [coeff_map, ← hs, ← hc, map_mul, map_natCast]

theorem frob_cong : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ b : ι → F.B, In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb b e)) - frob p F.s (cob1 (up F.Q μ') (comb b e))) := by
  intro p hp O _ hO _ ε F d μ' hμ ι _ e he b
  have hp0 : p ≠ 0 := hp.out.ne_zero
  set f := comb b e with hfdef
  set M := up F.Q μ' with hM
  have hM0 : ∀ i, constantCoeff (M i) = 0 := fun i => by
    rw [hM, up, constantCoeff_map, hμ.const i, map_zero]
  have hsM : HasSubst M := hasSubst_of_constantCoeff_zero hM0
  have hsL : HasSubst fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) F.Q) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hsR : HasSubst fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) F.Q) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

  have hX : ∀ (a : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.Q), (∀ i, ∃ j, a i = X j) → HasSubst a →
      subst a (frob p F.s f) = frob p F.s (subst a f) := by
    intro a ha has
    rw [subst_frob p hp0 F.s has, frob_subst p hp0 F.s has]
    congr 1
    funext i
    obtain ⟨j, hj⟩ := ha i
    rw [hj, map_X, expand_X]
  have hL := hX _ (fun i => ⟨_, rfl⟩) hsL
  have hR := hX _ (fun i => ⟨_, rfl⟩) hsR

  set u : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B := fun i => μ' i ^ p with hu
  set v : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B := fun i => expand p hp0 (map F.σ (μ' i)) with hv
  have hsalg : F.s.comp (algebraMap F.B F.Q) = (algebraMap F.B F.Q).comp F.σ :=
    RingHom.ext fun x => F.s_alg x
  have hup_u : up F.Q u = fun i => M i ^ p := by
    funext i; rw [up, hu, hM, up, map_pow]
  have hup_v : up F.Q v = fun i => expand p hp0 (map F.s (M i)) := by
    funext i; rw [up, hv, hM, up, map_expand, map_map, map_map, hsalg]
  have key : cob1 M (frob p F.s f) - frob p F.s (cob1 M f) =
      subst (up F.Q u) (map F.s f) - subst (up F.Q v) (map F.s f) := by
    rw [hup_u, hup_v, ← subst_frob p hp0 F.s hsM, ← frob_subst p hp0 F.s hsM]
    have hfs : ∀ a c : MvPowerSeries (Fin d ⊕ Fin d) F.Q,
        frob p F.s (a - c) = frob p F.s a - frob p F.s c := fun a c => by
      simp only [frob_eq_expand p hp0, map_sub]
    unfold cob1 inL inR
    rw [hfs, hfs, hL, hR]
    abel
  rw [key, ← Ideal.mul_top (Ideal.span {(p : F.B)})]
  have hnu : ¬IsUnit (p : F.B) := fun h => hO.out (by simpa using h.map F.θ)
  refine GlobalTheory.KatzCongr.subst_sub_in p F.B O F.Q F.θ F.frame _ ?_ (Fin d) (Fin d ⊕ Fin d) ⊤
    (map F.s f) u v ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨z ^ p * (p : F.B) ^ (p - 1),
      Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (Nat.sub_pos_of_lt hp.out.one_lt)), ?_⟩
    rw [mul_pow, mul_left_comm, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]
  · exact dIn_map F.σ F.s F.s_alg f
      (dIn_comb b e fun i => GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hμ ⊤ (e i) (he i))
  · intro i; rw [hu, map_pow, hμ.const i, zero_pow hp0]
  · intro i; rw [hv, constantCoeff_expand, constantCoeff_map, hμ.const i, map_zero]
  · intro i α
    exact coeff_pow_sub_expand_mem p hnu F.σ F.σ_pow (μ' i) α

end GlobalTheory.FrobCongr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffQuasiLogarithmIntegralLowDegree
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.QLogInt

theorem coeff_integral_of_QL : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ l : MvPowerSeries (Fin d) Q, QL μ ⊤ l → ∀ α : Fin d →₀ ℕ, α.degree ≤ p → (∀ i, α ≠ Finsupp.single i p) → ∃ b : B, coeff α l = algebraMap B Q b := by
  intro p hpf B O Q _ _ _ _ θ hF d μ hμ l hl α hdeg hne
  have hp : p.Prime := hpf.out
  classical
  by_cases h0 : α = 0
  · refine ⟨0, ?_⟩
    rw [h0, coeff_zero_eq_constantCoeff_apply, hl.1, map_zero]
  obtain ⟨k, hk⟩ : ∃ k, α k ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (Finsupp.ext h)
  have hkle : α k ≤ p := (Finsupp.le_degree k α).trans hdeg
  have hklt : α k < p := by
    refine lt_of_le_of_ne hkle fun hkp => hne k ?_
    have hs : Finsupp.single k p ≤ α := by
      rw [Finsupp.single_le_iff]; omega
    have hsplit : α = Finsupp.single k p + (α - Finsupp.single k p) := (add_tsub_cancel_of_le hs).symm
    have hd : (α - Finsupp.single k p).degree = 0 := by
      have h2 := congrArg Finsupp.degree hsplit
      rw [map_add (f := _), Finsupp.degree_single] at h2
      omega
    rw [(Finsupp.degree_eq_zero_iff _).1 hd, add_zero] at hsplit
    exact hsplit
  have hcop : Nat.Coprime (α k) p :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk) hklt)))
  obtain ⟨u, hu⟩ := hF.unit_coprime (α k) hcop
  obtain ⟨b', -, hb'⟩ := GlobalTheory.QLogDiff.dIn_of_QL p B O Q θ hF d μ hμ ⊤ l hl α k
  refine ⟨(↑u⁻¹ : B) * b', ?_⟩
  have h1 : algebraMap B Q (↑u⁻¹ : B) * (α k : Q) = 1 := by
    rw [← map_natCast (algebraMap B Q) (α k), ← hu, ← map_mul, Units.inv_mul, map_one]
  rw [map_mul, ← hb']
  linear_combination (-(coeff α l)) * h1

end GlobalTheory.QLogInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.red_c1_eq_c1_of_dvd : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1), red Q q E 2 1 (c1 Q L) = c1 q L := by
  first
  | exact @GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | exact GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | (intros; apply GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i)) → ContCone R F (sch.mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_of_affine_limit
  | exact GlobalTheory.EtC.contCone_of_affine_limit
  | (intros; apply GlobalTheory.EtC.contCone_of_affine_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHermitianFormUnitaryChartSection
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_eq_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun l => conj (v l)) := by
  simp only [hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ)
    (u v : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ v) = u ⬝ᵥ (gram τ G M *ᵥ fun l => conj (v l)) := by
  have hc : (fun l => conj ((M *ᵥ v) l)) = M.map (starRingEnd ℂ) *ᵥ fun l => conj (v l) := by
    funext l
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dot, hc, FrameDegreeData.gram_eq, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem gram_secM (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : V (nd X)}
    (hw : cpt X x w ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (secM X x w τ) = gram τ.1 X.Gm 1 := by
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  have hgx : secM X x w τ * mat x τ = mat (rmul (cpt X x w) (FrameDegreeData.bOf X (cpt X x w))) τ := by
    rw [secM, Matrix.nonsing_inv_mul_cancel_right _ _ hu, bOf_cpt X hx, yM, ← Matrix.mul_assoc]
    rfl
  have key : (mat x τ)ᵀ * gram τ.1 X.Gm (secM X x w τ) * (mat x τ).map (starRingEnd ℂ) =
      (mat x τ)ᵀ * gram τ.1 X.Gm 1 * (mat x τ).map (starRingEnd ℂ) := by
    rw [← FrameDegreeData.gram_mul, hgx, FrameDegreeData.ortho_bOf X hw τ, ← hx τ, ← FrameDegreeData.gram_mul, Matrix.one_mul]
  have huT : IsUnit (mat x τ)ᵀ.det := by rwa [Matrix.det_transpose]
  have huC : IsUnit ((mat x τ).map (starRingEnd ℂ)).det := by
    rw [show (mat x τ).map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (mat x τ) from rfl, ← RingHom.map_det, isUnit_iff_ne_zero, map_ne_zero]
    exact det_ne_of_orth X hx τ
  have h2 := congrArg (fun M => ((mat x τ)ᵀ)⁻¹ * M * ((mat x τ).map (starRingEnd ℂ))⁻¹) key
  simp only [Matrix.mul_assoc] at h2
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ huT, Matrix.mul_nonsing_inv_cancel_right _ _ huC,
    ← Matrix.mul_assoc] using h2

theorem hermC_secM (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : V (nd X)}
    (hw : cpt X x w ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (secM X x w τ *ᵥ u) (secM X x w τ *ᵥ v) = hermC τ.1 X.Gm u v := by
  rw [hermC_mulVec, gram_secM X hx hw τ, ← hermC_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

end GlobalTheory.SUChartSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSkewMemProductSpecialUnitaryLieAlgebra
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection

theorem conj_mem_realLie : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (Y : X.Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ a b, Y τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (Y τ a b) = 0) → (∀ τ a, Y τ a a = 0) → (fun τ => ((mat x τ * Y τ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ)) ∈ realLie X.Ψ X.Gm := by
  intro E _ _ _ r X x hx Y hY hd
  intro τ
  set A : Matrix (Fin r) (Fin r) ℂ := mat x τ with hAdef
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  set D : Matrix (Fin r) (Fin r) ℂ := A * Y τ * A⁻¹ with hDdef
  have hDA : D * A = A * Y τ := by
    rw [hDdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · change (A * Y τ * A⁻¹).trace = 0
    rw [Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    simp only [Matrix.trace, Matrix.diag, hd, Finset.sum_const_zero]
  · intro u w
    change hermC τ.1 X.Gm (D *ᵥ u) w + hermC τ.1 X.Gm u (D *ᵥ w) = 0
    clear_value D
    set Gt : Matrix (Fin r) (Fin r) ℂ := X.Gm.map τ.1 with hGt
    have hform : ∀ u v : Fin r → ℂ, hermC τ.1 X.Gm u v = u ⬝ᵥ (Gt *ᵥ (fun b => conj (v b))) := by
      intro u v
      simp only [hermC, dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [hGt, Matrix.map_apply]
      ring
    have hconj : ∀ v : Fin r → ℂ, (fun b => conj ((D *ᵥ v) b)) = D.map (starRingEnd ℂ) *ᵥ (fun b => conj (v b)) := by
      intro v
      funext b
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    set M : Matrix (Fin r) (Fin r) ℂ := Dᵀ * Gt + Gt * D.map (starRingEnd ℂ) with hMdef
    have hsum : hermC τ.1 X.Gm (D *ᵥ u) w + hermC τ.1 X.Gm u (D *ᵥ w) =
        u ⬝ᵥ (M *ᵥ (fun b => conj (w b))) := by
      rw [hform, hform, hconj, hMdef, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
      congr 1
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
    have hJ : Aᵀ * Gt * A.map (starRingEnd ℂ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
      rw [hGt, ← FrameDegreeData.gram_eq]
      exact hx τ
    have hkey : Aᵀ * M * A.map (starRingEnd ℂ) = 0 := by
      have e1 : Aᵀ * M * A.map (starRingEnd ℂ) =
          (D * A)ᵀ * Gt * A.map (starRingEnd ℂ) + Aᵀ * Gt * (D * A).map (starRingEnd ℂ) := by
        rw [hMdef, Matrix.transpose_mul, Matrix.map_mul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      have e2 : (D * A)ᵀ * Gt * A.map (starRingEnd ℂ) + Aᵀ * Gt * (D * A).map (starRingEnd ℂ) =
          (Y τ)ᵀ * (Aᵀ * Gt * A.map (starRingEnd ℂ)) + (Aᵀ * Gt * A.map (starRingEnd ℂ)) * (Y τ).map (starRingEnd ℂ) := by
        rw [hDA, Matrix.transpose_mul, Matrix.map_mul]
        simp only [Matrix.mul_assoc]
      rw [e1, e2, hJ]
      ext a b
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
        Matrix.map_apply, Matrix.zero_apply]
      exact hY τ a b
    have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
    have hAc : IsUnit (A.map (starRingEnd ℂ)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact hA.map _
    have hM : M = 0 := by
      calc M = Aᵀ⁻¹ * (Aᵀ * M * A.map (starRingEnd ℂ)) * (A.map (starRingEnd ℂ))⁻¹ := by
            rw [Matrix.mul_assoc Aᵀ, Matrix.nonsing_inv_mul_cancel_left _ _ hAt,
              Matrix.mul_nonsing_inv_cancel_right _ _ hAc]
        _ = 0 := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul]
    rw [hsum, hM, Matrix.zero_mulVec, dotProduct_zero]

end GlobalTheory.SUChartSection
end
end


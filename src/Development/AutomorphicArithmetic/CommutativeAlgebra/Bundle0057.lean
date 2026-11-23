module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerCoveringCongruenceOfHeckeLies
section
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.tower_covering_congruence_of_hecke_lies :
    MIn → SiteEx → NumEx → ClsEx → KSCover → TjLies → KSCong := by
  intro hM hS hN hC hV hL p _ D G L hsc E _ _ e gb hstd k T N J A _ g θ w 𝔴 hpl ϑ hG
  obtain ⟨q, r, 𝔫, K₀, hat, hok, hlev, hKN, hNn, hdeck, hall⟩ := hG
  haveI : Fact q.Prime := ⟨hat.prime⟩
  haveI : 𝔴.IsMaximal := hat.max
  obtain ⟨S⟩ := hS p D G hsc E e gb hstd w q r 𝔴 𝔫 hpl hat hok
  have hNpos : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  obtain ⟨c, a, hnum⟩ := (hN p D E gb w q r 𝔴 𝔫 S N.1 hNpos).1 hNn
  obtain ⟨⟨C⟩, -⟩ := hC q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat N.1 S.N₀ c a S.𝔞
    hnum.1 hNpos S.std.three S.std.cop hnum.2 S.Y (T.M N).X (T.M N).s (T.M N).univ
  obtain ⟨Cv⟩ := hV p D G L E gb w q r 𝔴 𝔫 S k T K₀ hlev N c a hnum C hKN J A g θ hdeck
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  haveI := S.et
  obtain ⟨Tc, Lc, d, h, hov, hpt⟩ := hM.cong q (datAt S.atq S.sp) (Ow w) S.f S.b S.N₀ r 𝔴 S.std S.M ϖ hϖ S.𝔞 1
    S.sup S.upow S.Y S.π S.ov inferInstance S.mπ k
  choose γ hγK hγT hγd hγr hγθ using hall
  refine ⟨Cv.toCover, q, S.f, hat.prime, S.qmem, S.norm, ϖ, fun j => (h j).corr,
    fun j => γ j (Nat.lt_succ_iff.1 j.2), fun j => (L.KN (g (γ j (Nat.lt_succ_iff.1 j.2))).M.1).relIndex
      (K₀ ⊓ K₀.comap (MulAut.conj (g (γ j (Nat.lt_succ_iff.1 j.2))).h).toMonoidHom), hϖ, hpt, fun j => ⟨hov j, ?_, ?_⟩⟩
  · obtain ⟨h0, κ, e1, e2, e3⟩ := hL p D G L E gb w q r 𝔴 𝔫 S k T K₀ hlev N c a hnum C hKN J g _ j
      (Nat.lt_succ_iff.1 j.2) (hγK _ _) (hγT _ _) (hγd _ _) (hγr _ _) (Tc j) (Lc j)
    exact ⟨h0, κ, e1, e2, e3⟩
  · exact hγθ _ _
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerFiniteEtaleOfTrivialPowerCartesian
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.Int.Geo

set_option maxHeartbeats 800000 in
theorem UpperTheory.tower_finiteEtale_of_trivial_powerCartesian :
    PiZero → PowCart → PiFet := by
  intro h0 hpc p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T N c a hN C
  obtain ⟨ρ, e0, hop, hcl, htr⟩ := h0 p D G L E gb w q r 𝔴 𝔫 S k T N c a hN C
  have hx : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have hN' : (N : ℕ) = S.N₀ * c := by
    unfold Site.Num at hN
    exact hN.1
  have hsub : ∀ (n m : ℕ) (g : G.GAf), L.CongOne (n * m) g → L.CongOne n g := by
    intro n m g hg
    unfold GlobalTheory.LKGeo.Link.CongOne at hg ⊢
    intro v hv
    obtain ⟨u, hu, huv⟩ := hg v hv
    exact ⟨m • u, AddSubgroup.nsmul_mem _ hu m, by rw [huv, mul_smul]⟩
  obtain ⟨hy, htr'⟩ : ∃ hy, T.X.tr (T.lev N) _ 1 hx hy ≫ ρ = _ := ⟨_, htr hx (by
    intro u hu
    rw [one_mul, inv_one, mul_one]
    rw [T.3] at hu ⊢
    rw [hN'] at hu
    show u ∈ L.KN S.N₀
    unfold GlobalTheory.LKGeo.Link.KN at hu ⊢
    exact ⟨hsub _ _ _ hu.1, hsub _ _ _ hu.2⟩)⟩
  have hG := S.mπ.3
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback at hG
  have hpb := hG.1
  obtain ⟨hP1, hP2, -⟩ := hpc S.Y.X S.M.X S.M.X S.Y.univ.A S.M.univ.A S.M.univ.A S.π (𝟙 _) S.mπ.φ (𝟙 _)
    hpb.w (by simp) k
  have hPB := hP1 hpb
  have hfinP : IsFinite (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hPB.flip S.20
  have hetP : Etale (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) :=
    MorphismProperty.of_isPullback (P := @Etale) hPB.flip S.21
  have hcomm : (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s =
      GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s := by
    rw [← Category.assoc, hP2, Category.assoc, S.18]
  have eY : S.pi T C ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s = T.X.q (T.lev N) ≫ gen (Ow w) E := by
    rw [hcomm, ← Category.assoc, ← htr', Category.assoc, e0, ← Category.assoc, T.X.10]
  refine ⟨eY, ?_⟩
  have h1 : ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) ≫ 𝟙 _ =
      GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s := by
    rw [Category.comp_id, hcomm]
  have h2 : gen (Ow w) E ≫ 𝟙 _ = 𝟙 _ ≫ gen (Ow w) E := by
    rw [Category.comp_id, Category.id_comp]
  let hm := pullback.map ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) (gen (Ow w) E)
    ((GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s) (gen (Ow w) E)
    (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) (𝟙 _) (𝟙 _) h1 h2
  have h3 : gen (Ow w) E = 𝟙 _ ≫ gen (Ow w) E := (Category.id_comp _).symm
  have hmF : IsFinite hm := MorphismProperty.pullbackMap (P := @IsFinite) hfinP inferInstance hcomm h3
  haveI := hetP
  have hmU : FormallyUnramified hm :=
    MorphismProperty.pullbackMap (P := @FormallyUnramified) inferInstance inferInstance hcomm h3
  have hkey : pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm =
      T.X.tr _ _ 1 hx hy ≫ pullback.lift ρ _ e0 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, htr']
      simp only [hm, pullback.lift_fst_assoc, pullback.map, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, T.X.10]
      simp only [hm, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  haveI := hop
  haveI := hcl
  haveI := T.X.13 _ _ hx hy
  haveI := T.X.14 _ _ hx hy
  have hcomp : IsFinite (pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm) ∧
      Etale (pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm) := by
    rw [hkey]
    exact ⟨inferInstance, inferInstance⟩
  haveI := hcomp.1
  haveI := hcomp.2
  exact ⟨IsFinite.of_comp _ hm, Etale.of_comp _ hm⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerInvariantOfBaseInvariantPowerCartesian
section
open UpperTheory.Gal.Int.Geo
open CategoryTheory AlgebraicGeometry

private theorem powMap_congr {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f f' : S' ⟶ S} {φ φ' : A'.left ⟶ A.left}
    (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f) (h' : φ' ≫ A.hom = A'.hom ≫ f') (k : ℕ) :
    GlobalTheory.KS.powMap f φ h k = GlobalTheory.KS.powMap f' φ' h' k := by
  subst hf hφ
  rfl

theorem UpperTheory.tower_invariant_of_base_invariant_powerCartesian :
    BaseInv → PowCart → PiInv := by
  intro hB hP p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu x y
  obtain ⟨π, o, ψ, φ, hw, ov, tr, e⟩ := T.tr_eq N' N u x y
  obtain ⟨h1, h2⟩ := hB p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu
    ⟨π, o, ψ, φ, ov, tr⟩
  have h1' : π ≫ C.j = C'.j := h1
  have h2' : (ψ.left ≫ φ.φ) ≫ C.m.φ = C'.m.φ := by
    rw [Category.assoc]; exact h2
  have hv := C.m.cart.1.w
  have hw' : ((ψ.left ≫ φ.φ) ≫ C.m.φ) ≫ S.Y.univ.A.hom = (T.M N').univ.A.hom ≫ π ≫ C.j := by
    rw [Category.assoc, hv, ← Category.assoc, hw, Category.assoc]
  have hc := (hP _ _ _ (T.M N').univ.A (T.M N).univ.A S.Y.univ.A π C.j (ψ.left ≫ φ.φ) C.m.φ hw hv k).2.2 hw'
  simp only [Site.pi, Cls.pw]
  rw [← Category.assoc, e, Category.assoc, hc]
  exact congrArg _ (powMap_congr h1' h2' _ _ k)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerPointCountStatement
section
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.tower_point_count_statement :
    Count := by
  intro Γ _ K₀ H K hKH hHK₀ hK F κ hF hκ ζ
  classical
  have hmul : K.relIndex H * H.relIndex K₀ = K.relIndex K₀ :=
    Subgroup.relIndex_mul_relIndex K H K₀ hKH hHK₀
  have hKH0 : K.relIndex H ≠ 0 := fun h0 => hK (by rw [← hmul, h0, zero_mul])
  have hH0 : H.relIndex K₀ ≠ 0 := fun h0 => hK (by rw [← hmul, h0, mul_zero])
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact hH0)
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite (↥K₀ ⧸ K.subgroupOf K₀) := Nat.finite_of_card_ne_zero hK
  haveI : Finite (↥H ⧸ K.subgroupOf H) := Nat.finite_of_card_ne_zero hKH0
  have bound : ∀ ξ : F, Nat.card {x // κ x = ξ} ≤ K.relIndex H := by
    intro ξ
    by_cases hne : Nonempty {x // κ x = ξ}
    · obtain ⟨⟨q0, hq0⟩⟩ := hne
      have memH : ∀ q : {x // κ x = ξ},
          ((q0.out : ↥K₀) : Γ)⁻¹ * ((q.1.out : ↥K₀) : Γ) ∈ H := by
        intro q
        apply hκ
        rw [QuotientGroup.out_eq', QuotientGroup.out_eq', hq0, q.2]
      let f : {x // κ x = ξ} → ↥H ⧸ K.subgroupOf H := fun q => ((⟨_, memH q⟩ : ↥H) : ↥H ⧸ K.subgroupOf H)
      have hinj : Function.Injective f := by
        intro q1 q2 h12
        have h' := QuotientGroup.eq.mp h12
        rw [Subgroup.mem_subgroupOf] at h'
        apply Subtype.ext
        rw [← QuotientGroup.out_eq' q1.1, ← QuotientGroup.out_eq' q2.1]
        apply QuotientGroup.eq.mpr
        rw [Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using h'
      calc Nat.card {x // κ x = ξ} ≤ Nat.card (↥H ⧸ K.subgroupOf H) :=
            Nat.card_le_card_of_injective f hinj
        _ = K.relIndex H := rfl
    · haveI := not_nonempty_iff.mp hne
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  have hsum : ∑ ξ : F, Nat.card {x // κ x = ξ} = ∑ ξ : F, K.relIndex H := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv κ), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hF, mul_comm, hmul]
    rfl
  exact (Finset.sum_eq_sum_iff_of_le (fun ξ _ => bound ξ)).mp hsum ζ (Finset.mem_univ _)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TowerSeparatedOfTrivialPowerCartesian
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private theorem kn_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N : ℕ} {k u : G.GAf}
    (hk : k ∈ L.KN 1) (hu : u ∈ L.KN N) : k * u * k⁻¹ ∈ L.KN N := by
  have key : ∀ g : G.GAf, L.CongOne 1 g → L.CongOne 1 g⁻¹ → ∀ x : G.GAf, L.CongOne N x →
      L.CongOne N (g * x * g⁻¹) := by
    intro g hg hg' x hx
    unfold Link.CongOne at hg hg' hx ⊢
    intro v hv
    obtain ⟨w₁, hw₁, h₁⟩ := hg' v hv
    have hv₁ : L.actG g⁻¹ v ∈ LaHat D := by
      rw [h₁, one_smul]
      exact add_mem hv hw₁
    obtain ⟨w₂, hw₂, h₂⟩ := hx _ hv₁
    obtain ⟨w₃, hw₃, h₃⟩ := hg w₂ hw₂
    refine ⟨w₂ + w₃, add_mem hw₂ hw₃, ?_⟩
    have hgg : L.actG g (L.actG g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₂, map_add (f := _), hgg, map_nsmul, h₃,
      one_smul]
  have hk' : L.CongOne 1 k ∧ L.CongOne 1 k⁻¹ := hk
  have hu' : L.CongOne N u ∧ L.CongOne N u⁻¹ := hu
  show L.CongOne N (k * u * k⁻¹) ∧ L.CongOne N (k * u * k⁻¹)⁻¹
  refine ⟨key k hk'.1 hk'.2 u hu'.1, ?_⟩
  have hinv : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
  rw [hinv]
  exact key k hk'.1 hk'.2 u⁻¹ hu'.2

private theorem gen_mono {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Mono (gen (Ow w) E) := by
  haveI : Epi (CommRingCat.ofHom (algebraMap (Ow w) E)) := IsLocalization.epi (nonZeroDivisors (Ow w)) E
  change Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap (Ow w) E)).op)
  infer_instance

theorem UpperTheory.tower_separated_of_trivial_powerCartesian :
    PiZero → BaseSep → PowCart → PiSep := by
  intro hPZ hBS hPC p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C Ω _ _ z z' hz
  obtain ⟨ρ, e, hopen, -, htr⟩ := hPZ p D G L E gb w q r 𝔴 𝔫 S k T N c a hNum C
  have hKM := T.K_eq ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩
  revert hKM
  revert ρ
  generalize T.lev ⟨S.N₀, PiZero._proof_1 p D E gb w q r 𝔴 𝔫 S⟩ = M
  intro ρ e hopen htr hKM
  have x : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have y : ∀ u ∈ T.X.K (T.lev N), 1 * u * 1⁻¹ ∈ T.X.K M := fun u hu => by
    have hN : S.N₀ ∣ (N : ℕ) := ⟨c, hNum.1⟩
    have hu' : u ∈ L.KN S.N₀ := KN_anti hN (by rw [← T.K_eq]; exact hu)
    rw [hKM]
    simpa using hu'
  have htr' := htr x y
  have hzM : z ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ ρ := by
    rw [htr', ← Category.assoc, hz, Category.assoc]
  have hzq : z ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M = z' ≫ T.X.tr (T.lev N) M 1 x y ≫ T.X.q M := by
    haveI : Mono (gen (Ow w) E) := gen_mono w
    rw [← cancel_mono (gen (Ow w) E)]
    simp only [Category.assoc]
    rw [← e]
    simp only [← Category.assoc] at hzM ⊢
    rw [hzM]
  have hzt : z ≫ T.X.tr (T.lev N) M 1 x y = z' ≫ T.X.tr (T.lev N) M 1 x y := by
    haveI := hopen
    rw [← cancel_mono (pullback.lift ρ (T.X.q M) e)]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact hzM
    · simp only [Category.assoc, pullback.lift_snd]
      exact hzq
  have hnorm : ∀ g ∈ T.X.K M, ∀ u ∈ T.X.K (T.lev N), g * u * g⁻¹ ∈ T.X.K (T.lev N) := by
    intro g hg u hu
    rw [hKM] at hg
    rw [T.K_eq] at hu ⊢
    exact kn_conj L (KN_anti (one_dvd _) hg) hu
  obtain ⟨g, hg, a', b', hz'⟩ := T.X.trans (T.lev N) M x y hnorm Ω z z' hzt
  refine ⟨g, ?_, a', b', hz'⟩
  rw [hKM] at hg
  obtain ⟨π, o, ψ, φ, hw, hπ, htrans, heq⟩ := T.tr_eq N N g a' b'
  have hP2 := (hPC _ _ _ (T.M N).univ.A (T.M N).univ.A (T.M N).univ.A π (𝟙 _) (Over.Hom.left ψ ≫ φ.φ)
    (𝟙 _) hw (by simp) k).2.1
  have hP3 : Cls.pw C k ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom = (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j :=
    (hPC _ _ _ (T.M N).univ.A S.Y.univ.A S.Y.univ.A C.j (𝟙 _) C.m.φ (𝟙 _) _ (by simp) k).2.1
  have h1 : z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom =
      z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ π := by
    rw [hz', Category.assoc, reassoc_of% heq, hP2]
  have h2 : z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j =
      z' ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom ≫ C.j := by
    have hz2 := hz
    unfold Site.pi at hz2
    rw [← hP3]
    simp only [← Category.assoc] at hz2 ⊢
    rw [hz2]
  refine hBS p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N c a hNum C g hg ⟨π, o, ψ, φ, hπ, htrans⟩ Ω
    (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ?_
  show (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ π ≫ C.j =
    (z ≫ (T.e N).hom ≫ (GlobalTheory.KS.pow (T.M N).univ.A k).hom) ≫ C.j
  simp only [Category.assoc]
  rw [h2, reassoc_of% h1]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaIdentity
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

private theorem sec_eq_of_points {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (n : ℕ) (hn : IsUnit (n : Γ(X, ⊤))) (σ σ' : 𝟙_ (Over X) ⟶ A) (h₁ : σ ^ n = 1) (h₂ : σ' ^ n = 1)
    (hpt : ∀ q : X, ∃ (k : Type) (_ : Field k) (y : Sp k ⟶ X), q ∈ Set.range y ∧
      toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ σ') : σ = σ' := by
  have key : ∀ q : X, ∃ V : X.Opens, q ∈ V ∧ V.ι ≫ σ.left = V.ι ≫ σ'.left := by
    intro q
    obtain ⟨k, hk, y, ⟨z, hz⟩, he⟩ := hpt q
    obtain ⟨V, hV, hVe⟩ := GlobalTheory.UPel.LocSim.exists_open_eq_of_torsion_point X A hA n hn σ σ' h₁ h₂ k y he
    exact ⟨V, hV ⟨z, hz⟩, hVe⟩
  choose V hV hVe using key
  have hcov : TopologicalSpace.IsOpenCover V := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun q _ => ?_)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨q, hV q⟩
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover V hcov) _ _ fun q => hVe q

private theorem map_nsmul_pow {M Q : Type} [AddCommGroup M] [Group Q] (f : M → Q) (hf : ∀ a b, f (a + b) = f a * f b)
    (m : ℕ) (a : M) : f (m • a) = f a ^ m := by
  induction m with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := f 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ m ih =>
    rw [succ_nsmul, hf, ih, pow_succ]

private theorem pow_comp_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {T A B : C} [GrpObj A] [GrpObj B]
    (a : T ⟶ A) (ψ : A ⟶ B) [IsMonHom ψ] (m : ℕ) : (a ≫ ψ) ^ m = (a ^ m) ≫ ψ := (map_pow (IsMonHom.monoidHom ψ T) a m).symm

private theorem ev_tower {G : GDatum} {k Q : Type} [Field k] [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : GTateIso G k Q act e) {M n c : ℕ} (hM : M = n * c) (hn : 0 < n) (hc : 0 < c) (z : G.La) :
    I.ev M (c • z) = I.ev n z := by
  subst hM
  rw [map_nsmul_pow (I.ev _) (I.add _)]
  exact I.tower n c hn hc z

theorem UpperTheory.trace_eta_identity : UpperTheory.Gal.Int.Geo.TrEta := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT n c' c hN' hN x y hxy
  haveI : IsMonHom ψ := hT.1
  have h3' := N'.2.1
  have h3 := N.2.1
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hN'; omega)
  have hc' : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN'; omega)
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hN; omega)
  have hcop : n.Coprime p := Nat.Coprime.coprime_dvd_left ⟨c', hN'⟩ N'.2.2
  have hunit : IsUnit (n : Γ(X, ⊤)) := by
    have hR : IsUnit (n : R) := by
      have hq : IsUnit (n : ℚ) := (Nat.cast_ne_zero.mpr hn.ne').isUnit
      simpa using hq.map (algebraMap ℚ R)
    have := hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using this
  have ex' : (n • c' • x : D.La) = (↑N' : ℕ) • x := by rw [smul_smul, ← hN']
  have ex : (n • c • y : D.La) = (↑N : ℕ) • y := by rw [smul_smul, ← hN]
  have e1 : (o'.eta (c' • x)) ^ n = 1 :=
    (map_nsmul_pow o'.eta o'.eta_add n (c' • x)).symm.trans ((congrArg o'.eta ex').trans (o'.eta_ker x))
  have hpow1 : (o'.eta (c' • x) ≫ ψ) ^ n = 1 :=
    (pow_comp_hom _ _ _).trans ((congrArg (· ≫ ψ) e1).trans (map_one (IsMonHom.monoidHom ψ _)))
  have hpow2 : (o.eta (c • y)) ^ n = 1 :=
    (map_nsmul_pow o.eta o.eta_add n (c • y)).symm.trans ((congrArg o.eta ex).trans (o.eta_ker y))
  refine sec_eq_of_points o.A o.ab n hunit _ _ hpow1 hpow2 (fun q => ?_)
  let κ := X.residueField q
  let k := AlgebraicClosure κ
  let y0 : Sp k ⟶ X := spMap (algebraMap κ k) ≫ X.fromSpecResidueField q
  let β : R →+* k := (Spec.preimage (y0 ≫ s)).hom
  have hβ : y0 ≫ s = spMap β := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (y0 ≫ s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨I', I'', hI', hI'', hiff⟩ := hT.2.2.2.2 k y0 β hβ
  refine ⟨k, inferInstance, y0, ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply q _⟩, ?_⟩
  calc toUnit (Over.mk y0) ≫ (o'.eta (c' • x) ≫ ψ)
      = (toUnit (Over.mk y0) ≫ o'.eta (c' • x)) ≫ ψ := (Category.assoc _ _ _).symm
    _ = I'.ev (↑N') (c' • x) ≫ ψ := congrArg (· ≫ ψ) (hI' _)
    _ = I'.ev n x ≫ ψ := congrArg (· ≫ ψ) (ev_tower I' hN' hn hc' x)
    _ = I''.ev n y := (hiff n hn hcop x y).mpr hxy
    _ = I''.ev (↑N) (c • y) := (ev_tower I'' hN hn hc y).symm
    _ = toUnit (Over.mk y0) ≫ o.eta (c • y) := (hI'' _).symm
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaPointwise
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.trace_eta_pointwise : TrEtaPt := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x
  obtain ⟨-, -, -, -, hgeo⟩ := hT
  have hz : z ≫ s = spMap (Spec.preimage (z ≫ s)).hom := by
    simp [spMap, Spec.map_preimage]
  obtain ⟨I', I'', h1, h2, h3⟩ := hgeo Ω z _ hz
  have hpos : ∀ M : Lv p, 0 < (M : ℕ) := fun M => by
    have := M.2.1
    omega
  have hzero : ∀ n : ℕ, I''.ev n 0 = 1 := fun n => by
    have h := I''.add n 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hin0 : inAf D 0 = 0 := by
    simp [inAf]
  have e1 := congrArg (· ≫ ψ) (h1 x)
  simp only [Category.assoc] at e1
  refine ⟨?_, ?_⟩
  · refine Iff.trans ?_ ((h3 _ (hpos N') N'.2.2 x 0).trans ?_)
    · rw [e1]
      first
        | simp only [hzero]
        | erw [hzero]
    · simp only [hin0, zero_add]
  · rintro rfl y hxy
    refine (h3 _ (hpos N') N'.2.2 x y).mp ?_
    rw [← e1, hxy]
    exact h2 y
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceUnitOfPullbackMultiplier
section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open UpperTheory.Gal.Int.Geo

private theorem unit_aux {A : Type} [CommRing A] {m c t t' s : A} (hm : m = c * t) (ht : t * t' = 1)
    (hs : m * s = 1) : c = 1 * (m * t') ∧ (m * t') * (t * s) = 1 := by
  constructor
  · rw [_root_.one_mul, hm, _root_.mul_assoc, ht, _root_.mul_one]
  · calc (m * t') * (t * s) = (m * s) * (t * t') := by ring
      _ = 1 := by rw [hs, ht, _root_.one_mul]

theorem UpperTheory.trace_unit_of_pullback_multiplier :
    TrBack → MultUnit → TrUnit := by
  intro hB hM p _ D G L R _ _ gb h X s N' N o' o ψ hT hh
  obtain ⟨ψ', -, e₁, e₂⟩ := hB p D G L R gb h X s N' N o' o ψ hT 1 (Nat.coprime_one_left p)
    (fun v hv => ⟨L.actG h⁻¹ v, integ_of_mem (inv_mem hh) v hv, by
      rw [one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩)
  have hiso : CategoryTheory.IsIso ψ := ⟨ψ', e₁.trans (pow_one _), e₂.trans (pow_one _)⟩
  refine ⟨hiso, ?_⟩
  obtain ⟨-, -, -, ⟨c, hc, hP, t, t', ht, ht', htt, hm⟩, -⟩ := hT
  obtain ⟨hu, hfix⟩ := hM p D G L
  obtain ⟨s', hi, hs, hs1⟩ := hu h hh
  obtain ⟨a₁, a₂⟩ := unit_aux hm htt hs1
  have hint : ∀ {a b : GlobalTheory.LKTrip.AfP p}, GlobalTheory.LKGeo.IsIntAf a → GlobalTheory.LKGeo.IsIntAf b → GlobalTheory.LKGeo.IsIntAf (a * b) := fun ha hb v => by
    rw [map_mul]; exact mul_mem (ha v) (hb v)
  have hc1 : c = 1 := hfix c 1 _ _ hc (Nat.coprime_one_left p) (hint hi ht') (hint ht hs) a₂
    (by rw [Nat.cast_one]; exact a₁)
  subst hc1
  exact hP
end


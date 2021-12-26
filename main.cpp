#include <bits/stdc++.h>

using namespace std;

struct bitmask {
    static const size_t SIZE = 4;
    
    array<uint64_t, SIZE> data;

    bitmask() {
        fill(data.begin(), data.end(), 0);
    };

    bitmask(const bitmask &b) = default;
    
    bitmask(uint64_t x) {
        fill(data.begin() + 1, data.end(), 0);
        data[0] = x;
    }

    bitmask operator&=(const bitmask &o) {
        for (size_t i = 0; i < SIZE; ++i) {
            data[i] &= o.data[i];
        }
        return *this;
    }

    bitmask operator^=(const bitmask &o) {
        for (size_t i = 0; i < SIZE; ++i) {
            data[i] ^= o.data[i];
        }
        return *this;
    }

    bitmask operator>>=(size_t x) {
        uint64_t div_offset = x / (sizeof(uint64_t) * 8);
        if (div_offset != 0) {
            for (size_t i = 0; i < SIZE - div_offset; ++i) {
                data[i] = data[i + div_offset];
            }
            for (size_t i = SIZE - div_offset; i < SIZE; ++i) {
                data[i] = 0;
            }
        }

        x %= sizeof(uint64_t) * 8;
        if (x == 0) {
            return *this;
        }
        uint64_t carry = 0;
        uint64_t next_carry;

        for (size_t i = SIZE; i-- > 0;) {
            next_carry = (data[i] << (sizeof(uint64_t) * 8 - x));
            data[i] = ((data[i] >> x) + carry);
            carry = next_carry;
        }

        return *this;
    }

    bitmask operator<<=(size_t x) {
        uint64_t div_offset = x / (sizeof(uint64_t) * 8);
        if (div_offset != 0) {
            for (size_t i = SIZE; i-- > div_offset;) {
                data[i] = data[i - div_offset];
            }
            for (size_t i = div_offset; i-- > 0;) {
                data[i] = 0;
            }
        }

        x %= sizeof(uint64_t) * 8;
        if (x == 0) {
            return *this;
        }
        uint64_t carry = 0;
        uint64_t next_carry;

        for (size_t i = 0; i < SIZE; ++i) {
            next_carry = (data[i] >> (sizeof(uint64_t) * 8 - x));
            data[i] = ((data[i] << x) + carry);
            carry = next_carry;
        }

        return *this;
    }

    void set(size_t i, uint64_t value) {
        if (value == 0) {
            data[i / (sizeof(uint64_t) * 8)] &= ~(1ULL << (i % (sizeof(uint64_t) * 8)));
        } else {
            data[i / (sizeof(uint64_t) * 8)] |= (1ULL << (i % (sizeof(uint64_t) * 8)));
        }
    }

    void flip(size_t i) {
        data[i / (sizeof(uint64_t) * 8)] ^= (1ULL << (i % (sizeof(uint64_t) * 8)));
    }

    uint64_t operator[](size_t i) const {
        return (data[i / (sizeof(uint64_t) * 8)] >> (i % (sizeof(uint64_t) * 8))) & 1ULL;
    }

    bool test(size_t i) const {
        return (*this)[i] == 1ULL;
    }

    uint64_t deg() const {
        for (size_t i = SIZE * (sizeof(uint64_t) * 8); i-- > 0;) {
            if (test(i)) {
                return i;
            }
        }
        return 0;
    };
};

string to_string(const bitmask &o) {
    string res;
    for (size_t i = 0; i <= o.deg(); ++i) {
        if (o.test(i)) {
            res += "x^" + to_string(i);
            if (i != o.deg()) {
                res += " + ";
            }
        }
    }
    return res;
}

struct bitmask_hash {
    size_t operator()(const bitmask& b) const {
        size_t seed = bitmask::SIZE;
        for(auto& i : b.data) {
            seed ^= i + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};

bool operator==(const bitmask &a, const bitmask &b) {
    return a.data == b.data;
}

bool operator!=(const bitmask &a, const bitmask &b) {
    return !(a == b);
}

bitmask operator&(bitmask a, const bitmask &b) {
    return a &= b;
}

bitmask operator^(bitmask a, const bitmask &b) {
    return a ^= b;
}

bitmask operator<<(bitmask a, size_t x) {
    return a <<= x;
}

bitmask multiply_polynomials(bitmask p1, bitmask p2) {
    bitmask res = 0;
    while (p2 != 0) {
        if (p2.test(0)) {
            res ^= p1;
        }
        p1 <<= 1ULL;
        p2 >>= 1ULL;
    }
    return res;
}

pair<bitmask, bitmask> div_polynomials(bitmask a, const bitmask &b) {
    uint64_t a_deg = a.deg() + 1;
    uint64_t b_deg = b.deg() + 1;
    bitmask div = 0;
    for (size_t i = a_deg; i >= b_deg; --i) {
        if (a.test(i - 1)) {
            a ^= b << (i - b_deg);
            div.set(i - b_deg, 1ULL);
        }
    }
    return {div, a};
}

struct gf {
    vector<bitmask> pow_to_polynomial;
    unordered_map<bitmask, uint64_t, bitmask_hash> polynomial_to_pow;
    uint64_t n;
    uint64_t m;

    gf(uint64_t n, const bitmask &pi) : n(n), m(0), pow_to_polynomial(n) {
        while (n > 0) {
            ++m;
            n /= 2;
        }
        n = this->n;
        bitmask limit(n + 1);
        bitmask modulo = pi ^ limit;
        bitmask alpha = 1;
        for (size_t i = 0; i < n; ++i) {
            pow_to_polynomial[i] = alpha;
            polynomial_to_pow[alpha] = i;
            alpha <<= 1;
            if ((alpha & limit) != 0ULL) {
                alpha ^= limit;
                alpha ^= modulo;
            }
        }
    }

    uint64_t inverse(uint64_t pow) const {
        return (n - pow) % n;
    }

    uint64_t to_pow(const bitmask &polynomial) const {
        return polynomial_to_pow.find(polynomial)->second;
    }

    bitmask to_poly(uint64_t pow) const {
        return pow_to_polynomial[pow % n];
    }

    bitmask multiply_poly(const bitmask &poly1, const bitmask &poly2) const {
        if (poly1 == 0 || poly2 == 0) {
            return 0;
        }
        return pow_to_polynomial[(polynomial_to_pow.find(poly1)->second + polynomial_to_pow.find(poly2)->second) % n];
    }

    uint64_t multiply_pow(uint64_t pow1, uint64_t pow2) const {
        return (pow1 + pow2) % n;
    }
};

struct coder {
    bitmask g;
    uint64_t n, r, k, d;
    gf gf2;

    coder(uint64_t n, const bitmask &pi, uint64_t d) : n(n), d(d), gf2(n, pi) {
        unordered_set<bitmask, bitmask_hash> minimal_polynomials;
        for (uint64_t i = 1; i < d; i += 2) {
            minimal_polynomials.insert(minimal_polynomial(i));
        }
        g = 1;
        for (const auto &m : minimal_polynomials) {
            g = multiply_polynomials(g, m);
        }
        r = g.deg();
        k = n - r;
    }

    bitmask encode(const bitmask &a) const {
        return (a << r) ^ div_polynomials(a << r, g).second;
    }

    bitmask decode(bitmask &y) const {
        vector<bitmask> s;
        for (uint64_t i = 1; i < d; ++i) {
            s.push_back(syndrome(y, i));
        }
        auto p = berlekamp_massey(s);
        unordered_map<uint64_t, uint64_t> lambda_pows;
        for (size_t i = 0; i < p.second.size(); ++i) {
            if (p.second[i] != 0) {
                lambda_pows[i] = gf2.to_pow(p.second[i]);
            }
        }
        vector<uint64_t> corr_pos;
        for (uint64_t i = 0; i < n; ++i) {
            bitmask acc = 0;
            for (const auto &pow : lambda_pows) {
                acc ^= gf2.to_poly(gf2.multiply_pow(pow.second, i * pow.first));
            }
            if (acc == 0) {
                corr_pos.push_back((n - i) % n);
            }
        }
        if (corr_pos.size() != p.first) {
            throw runtime_error("FAILURE");
        }
        for (uint64_t pos : corr_pos) {
            y.flip(pos);
        }
        return y;
    }

    bitmask syndrome(const bitmask &y, uint64_t u) const {
        bitmask ans = 0;
        uint64_t deg = y.deg();
        for (size_t p = 0; p <= deg; ++p) {
            if (y.test(p)) {
                ans ^= gf2.to_poly(p * u);
            }
        }
        return ans;
    }

    pair<uint64_t, vector<bitmask>> berlekamp_massey(const vector<bitmask> &s) const {
        vector<bitmask> lambda(1, 1ULL);
        uint64_t l = 0, m = 0;
        vector<bitmask> b(1, 1ULL);

        for (uint64_t r = 1; r <= d - 1; ++r) {
            bitmask delta_r = 0;
            for (size_t j = 0; j <= l; ++j) {
                delta_r ^= gf2.multiply_poly(lambda[j], s[r - 1 - j]);
            }
            if (delta_r != 0) {
                vector<bitmask> t(max(static_cast<uint64_t>(lambda.size()), static_cast<uint64_t>(b.size() + (r - m))));
                for (size_t i = 0; i < min(static_cast<uint64_t>(lambda.size()), static_cast<uint64_t>(b.size() + (r - m))); ++i) {
                    t[i] = lambda[i] ^ ((i < r - m) ? 0 : gf2.multiply_poly(delta_r, b[i - (r - m)]));
                }
                for (size_t i = min(static_cast<uint64_t>(lambda.size()), static_cast<uint64_t>(b.size() + (r - m))); i < max(static_cast<uint64_t>(lambda.size()), static_cast<uint64_t>(b.size() + (r - m))); ++i) {
                    t[i] = i < lambda.size() ? lambda[i] : ((i < r - m) ? 0 : gf2.multiply_poly(delta_r, b[i - (r - m)]));
                }
                if (2 * l <= r - 1) {
                    b.resize(lambda.size());
                    for (size_t i = 0; i < lambda.size(); ++i) {
                        if (lambda[i] == 0) {
                            b[i] = 0;
                        } else {
                            b[i] = gf2.to_poly(gf2.multiply_pow(gf2.inverse(gf2.to_pow(delta_r)),
                                                                gf2.to_pow(lambda[i])));
                        }
                    }
                    l = r - l;
                    m = r;
                }
                lambda = t;
            }
        }
        return {l, lambda};
    }

    bitmask minimal_polynomial(uint64_t primitive_pow) const {
        bitmask ans = 0;
        vector<uint64_t> pows(1, primitive_pow);
        for (;;) {
            uint64_t pow = gf2.multiply_pow(pows.back(), pows.back());
            if (pow == primitive_pow) {
                break;
            }
            pows.push_back(pow);
        }
        vector<bitmask> polynomial(pows.size() + 1);
        polynomial.back() = 1;
        polynomial[polynomial.size() - 1] = 1;
        for (uint64_t i = 1; i < (1ULL << pows.size()); ++i) {
            uint64_t ic = i;
            size_t bits_cnt = 0;
            size_t u = 0;
            uint64_t acc = 0;
            while (ic != 0) {
                if ((ic & 1ULL) == 1ULL) {
                    ++bits_cnt;
                    acc = gf2.multiply_pow(acc, pows[u]);
                }
                ++u;
                ic >>= 1ULL;
            }
            polynomial[pows.size() - bits_cnt] ^= gf2.to_poly(acc);
        }
        for (size_t i = 0; i < polynomial.size(); ++i) {
            ans.set(i, polynomial[i][0]);
        }
        return ans;
    }
};

bitmask read_word(size_t k) {
    bitmask result = 0;
    for (int i = 0; i < k; ++i) {
        uint64_t bit;
        cin >> bit;
        result.set(i, bit);
    }
    return result;
}

void print_word(size_t n, const bitmask &word) {
    for (size_t i = 0; i < n; ++i) {
        cout << word[i] << ' ';
    }
}

int main() {
    freopen("input.txt", "r", stdin);
    freopen("output.txt", "w", stdout);
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    uint64_t n, pi, d;
    cin >> n >> pi >> d;
    coder c(n, pi, d);
    cout << c.k << '\n';
    print_word(c.r + 1, c.g);
    cout << '\n';

    mt19937 gen;
    bernoulli_distribution coin(0.5);

    string command;
    while (cin >> command) {
        if (command == "Encode") {
            bitmask word = read_word(c.k);
            print_word(n, c.encode(word));
        } else if (command == "Decode") {
            try {
                bitmask word = read_word(n);
                print_word(n, c.decode(word));
            } catch (const runtime_error &e) {
                cout << "ERROR";
            }
        } else if (command == "Simulate") {
            double noise_level;
            size_t num_of_iterations, max_errors;
            cin >> noise_level >> num_of_iterations >> max_errors;

            bernoulli_distribution b_dist(noise_level);
            size_t total_iterations, total_errors = 0;
            for (total_iterations = 0; total_iterations < num_of_iterations &&
                                       total_errors < max_errors; ++total_iterations) {
                bitmask word = 0;
                for (size_t i = 0; i < n; ++i) {
                    if (coin(gen)) {
                        word.flip(i);
                    }
                }
                bitmask code = c.encode(word);
                bitmask noised_code = code;
                for (size_t i = 0; i < n; ++i) {
                    if (b_dist(gen)) {
                        noised_code.flip(i);
                    }
                }
                try {
                    bitmask received_code = c.decode(noised_code);
                    if (code != received_code) {
                        ++total_errors;
                    }
                } catch (const runtime_error &e) {
                    ++total_errors;
                }
            }

            cout << static_cast<double>(total_errors) / static_cast<double>(total_iterations);
        }
        cout << '\n';
    }
}

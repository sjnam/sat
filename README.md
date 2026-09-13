# Go를 위한 SAT 꾸러미

크누스가 『The Art of Computer Programming』 7.2.2.2절을 준비하며 쓴 SAT
풀이기들 가운데 가장 빠른
[**SAT13**](https://www-cs-faculty.stanford.edu/~knuth/programs/sat13.w)
(알고리즘 7.2.2.2C, CDCL)을 Go 꾸러미로 옮기는 중이다.

크누스의 프로그램은 표준 입력으로 절을 받는 명령이다. 이 꾸러미는 같은 알맹이를
다른 Go 프로그램이 절을 넘기고 답을 받을 수 있는 라이브러리로 만든다. 옮기는
원칙은 하나다. **같은 입력과 같은 매개변수에서 mem 수가 C 원본과 똑같이 나와야
한다.**

## 진행

| 단계 | 글 | 내용 | 상태 |
|---|---|---|---|
| 1 | `sat.w` | 리터럴, 풀이기의 겉모습, 절 쌓기 | 완료 |
| 1 | `io.w` | 크누스 형식과 DIMACS 형식 읽기 | 완료 |
| 2 | `cdcl.w` | SAT13의 알맹이: 강제, 활동도, 충돌 학습, 절 치우기 | 다음 |
| 3 | `simplify.w` | SAT12 전처리와 SAT12-ERP 되살림 | |
| 4 | | 가정 리터럴을 쓰는 점진적 풀이 | |

## 맛보기 (지금 되는 것)

```go
s := sat.New()
x, y := s.NewVar(), s.Lookup("y") // 이름 없는 변수와 이름 있는 변수
s.AddClause(x, y.Not())
s.AddClause(y)

f, _ := os.Open("foo.cnf")
err := s.ReadDIMACS(f) // 또는 s.ReadKnuth(f)
```

리터럴은 크누스를 따라 변수 k에 대해 `2k`(양)와 `2k+1`(음)이다.
변수 번호는 이름이 처음 나온 차례로 매겨진다. DIMACS 변수 k의 이름은 `"k"`다.

## 만들기

`.w`를 손보려면 [GWEB](https://github.com/sjnam/gweb)이 필요하다.

```sh
make          # .w를 Go로 짜내고 빌드한다
make test     # 시험을 돌린다
make pdf      # 문학적 문서를 조판한다
make check    # 조판 로그에 경고가 하나도 없는지 확인한다
```

크누스의 벤치마크 전부로 시험하려면
[SATexamples.tgz](https://www-cs-faculty.stanford.edu/~knuth/programs/SATexamples.tgz)를
풀어 두고 `SATEXAMPLES=<그 디렉터리> go test ./...`처럼 돌린다.

## 파일

- `knuth/`: 크누스의 원본 CWEB 프로그램 (sat0w, sat8, sat11, sat11k, sat12,
  sat12-erp, sat13, dimacs-to-sat, sat-to-dimacs)
- `testdata/`: SATexamples에서 고른 작은 문제 여섯, 두 형식으로 하나씩

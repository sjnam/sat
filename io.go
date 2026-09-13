//line io.w:22
package sat

import (
	"bufio"
	"fmt"
	"io"
	"strconv"
)

//line io.w:41
type ParseError struct {
	Line int    // 잘못이 난 줄, 1부터 센다
	Msg  string // 무엇이 잘못인가
}

//line io.w:47
func (e *ParseError) Error() string {
	return fmt.Sprintf("sat: %d번째 줄: %s", e.Line, e.Msg)
}

//line io.w:88
func (s *Solver) ReadKnuth(r io.Reader) error {
	sc := bufio.NewScanner(r)
	sc.Buffer(nil, 1<<30)
	line := 0
lines:
	for sc.Scan() {
		line++
		buf := sc.Bytes()
		s.beginClause()
		for j := 0; ; {
			for j < len(buf) && buf[j] == ' ' {
				j++
			}
			if j == len(buf) {
				break
			}

//line io.w:120
			if buf[j] < ' ' || buf[j] > '~' {
				return &ParseError{line, fmt.Sprintf("쓸 수 없는 글자 %#02x", buf[j])}
			}
			neg := buf[j] == '~'
			if neg {
				j++
			}
			i := j
			for j < len(buf) && buf[j] > ' ' && buf[j] <= '~' {
				j++
			}
			if i == j {
				s.cells = s.cells[:s.start]
				continue lines
			}

//line io.w:142
			if buf[i] == '~' {
				return &ParseError{line, fmt.Sprintf("이름 %q가 ~로 시작한다", buf[i:j])}
			}
			v, ok := s.index[string(buf[i:j])]
			if !ok {
				v = s.Lookup(string(buf[i:j])).Var()
			}
			l := Pos(v)
			if neg {
				l = l.Not()
			}

//line io.w:105
			if !s.addLit(l) {
				continue lines
			}
		}
		if len(s.cells) > s.start {
			s.endClause()
		}
	}
	return sc.Err()
}

//line io.w:183
func (s *Solver) ReadDIMACS(r io.Reader) error {
	sc := bufio.NewScanner(r)
	sc.Buffer(nil, 1<<30)
	var dimacs []int
	open, dead := false, false
	line := 0
lines:
	for sc.Scan() {
		line++
		buf := sc.Bytes()

//line io.w:208
		j := 0
		for j < len(buf) && (buf[j] == ' ' || buf[j] == '\t') {
			j++
		}
		switch {
		case j == len(buf) || buf[j] == 'c':
			continue
		case buf[j] == '%':
			break lines
		case buf[j] == 'p':

//line io.w:235
			if dimacs != nil {
				return &ParseError{line, "머리줄이 두 번 나왔다"}
			}
			var n, m int
			_, err := fmt.Sscanf(string(buf[j:]), "p cnf %d %d", &n, &m)
			if err != nil || n < 0 || n > maxVar || m < 0 {
				return &ParseError{line, "머리줄은 `p cnf 변수의수 절의수' 꼴이어야 한다"}
			}
			dimacs = make([]int, n+1)

//line io.w:219
			continue
		case dimacs == nil:
			return &ParseError{line, "p cnf 머리줄보다 절이 먼저 나왔다"}
		}
		for {
			for j < len(buf) && (buf[j] == ' ' || buf[j] == '\t') {
				j++
			}
			if j == len(buf) {
				break
			}

//line io.w:250
			neg := buf[j] == '-'
			if neg {
				j++
			}
			i, x := j, 0
			for j < len(buf) && '0' <= buf[j] && buf[j] <= '9' && x <= maxVar {
				x = x*10 + int(buf[j]-'0')
				j++
			}
			if i == j || (j < len(buf) && buf[j] != ' ' && buf[j] != '\t') {
				return &ParseError{line, "정수가 아닌 것이 있다"}
			}
			if x >= len(dimacs) {
				return &ParseError{line, fmt.Sprintf("변수 %d가 머리줄의 %d보다 크다", x, len(dimacs)-1)}
			}

//line io.w:231

//line io.w:270
			if !open {
				s.beginClause()
				open, dead = true, false
			}
			if x == 0 {
				if !dead {
					s.endClause()
				}
				open = false
				continue
			}
			if dead {
				continue
			}
			if dimacs[x] == 0 {
				dimacs[x] = s.Lookup(strconv.Itoa(x)).Var()
			}
			l := Pos(dimacs[x])
			if neg {
				l = l.Not()
			}
			dead = !s.addLit(l)

//line io.w:232
		}

//line io.w:194
	}
	if err := sc.Err(); err != nil {
		return err
	}
	if open && !dead {
		s.endClause()
	}
	return nil
}

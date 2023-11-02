package iter

func Exec(fs Iterator[func()]) {
	for fs.Next() {
		m := fs.Current()
		m()
	}
}

// I executes all members of fs until the last or until it finds the first false guard
// guard is called before every execution of fs members
func I(guard func() bool, fs ...func()) (reachedLast bool) {
	i := 0
	for i != len(fs) && guard() {
		fs[i]()
		i = i + 1
	}
	reachedLast = i == len(fs)
	return
}

// W it executes repeteadly all members of fs until it finds the first false guard
// guard is called before every execution of fs members
func W(guard func() bool, fs ...func()) {
	i, do := 0, len(fs) != 0
	for do {
		if i == len(fs) {
			i = 0
		}
		fs[i]()
		i = i + 1
		do = guard()
	}
}

package main

import "fmt"

func main() {
	var n = 5
	fmt.Print(n)
	var m = 8
	fmt.Print(m)
	n, m = m, n
	fmt.Print(n)
	fmt.Print(m)

}

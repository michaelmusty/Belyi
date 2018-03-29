s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T2-[3,3,3]-333-333-333-g1";
s`BelyiDBFilename := "9T2-[3,3,3]-333-333-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 3, 3, 3 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 9 > |
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
[ 3, 4, 8, 6, 7, 2, 9, 1, 5 ],
[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 9, 1, 5, 3, 4, 8, 6, 7, 2 ],
\[ 8, 6, 1, 2, 9, 4, 5, 3, 7 ]:
 Order := 9 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 3 >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 3, 4, 8, 6, 7, 2, 9, 1, 5 ],
\[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]:
 Order := 9 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 3, 4, 8, 6, 7, 2, 9, 1, 5 ],
\[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]:
 Order := 9 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 3, 4, 8, 6, 7, 2, 9, 1, 5 ],
\[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]:
 Order := 9 > |
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
[ 3, 4, 8, 6, 7, 2, 9, 1, 5 ],
[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 9 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 9 > |
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
[ 3, 4, 8, 6, 7, 2, 9, 1, 5 ],
[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;

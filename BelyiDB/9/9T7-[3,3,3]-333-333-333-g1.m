s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T7-[3,3,3]-333-333-333-g1";
s`BelyiDBFilename := "9T7-[3,3,3]-333-333-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 3, 3, 3 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 27 > |
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
[ 4, 5, 8, 6, 7, 1, 2, 9, 3 ],
[ 5, 3, 8, 6, 7, 9, 1, 2, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 3 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 4, 5, 8, 6, 7, 1, 2, 9, 3 ],
\[ 5, 3, 8, 6, 7, 9, 1, 2, 4 ]:
 Order := 27 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 4, 5, 8, 6, 7, 1, 2, 9, 3 ],
\[ 5, 3, 8, 6, 7, 9, 1, 2, 4 ]:
 Order := 27 >) |
[ PermutationGroup<9 |  
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 4, 5, 8, 6, 7, 1, 2, 9, 3 ],
\[ 5, 3, 8, 6, 7, 9, 1, 2, 4 ]:
 Order := 27 > |
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
[ 4, 5, 8, 6, 7, 1, 2, 9, 3 ],
[ 5, 3, 8, 6, 7, 9, 1, 2, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 27 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 27 > |
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
[ 4, 5, 8, 6, 7, 1, 2, 9, 3 ],
[ 5, 3, 8, 6, 7, 9, 1, 2, 4 ]
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

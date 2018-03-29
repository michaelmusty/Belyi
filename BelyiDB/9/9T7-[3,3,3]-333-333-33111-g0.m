s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T7-[3,3,3]-333-333-33111-g0";
s`BelyiDBFilename := "9T7-[3,3,3]-333-333-33111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 3, 3, 3 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 27 > |
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
[ 6, 7, 9, 1, 2, 4, 5, 3, 8 ],
[ 2, 9, 3, 4, 5, 8, 6, 7, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 3 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 7, 9, 1, 2, 4, 5, 3, 8 ],
\[ 2, 9, 3, 4, 5, 8, 6, 7, 1 ]:
 Order := 27 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 7, 9, 1, 2, 4, 5, 3, 8 ],
\[ 2, 9, 3, 4, 5, 8, 6, 7, 1 ]:
 Order := 27 >) |
[ PermutationGroup<9 |  
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 7, 9, 1, 2, 4, 5, 3, 8 ],
\[ 2, 9, 3, 4, 5, 8, 6, 7, 1 ]:
 Order := 27 > |
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
[ 6, 7, 9, 1, 2, 4, 5, 3, 8 ],
[ 2, 9, 3, 4, 5, 8, 6, 7, 1 ]
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
[ 6, 7, 9, 1, 2, 4, 5, 3, 8 ],
[ 2, 9, 3, 4, 5, 8, 6, 7, 1 ]
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
